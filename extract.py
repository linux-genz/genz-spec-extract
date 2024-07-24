#!/usr/bin/env python3

# Copyright (c) 2020 Hewlett Packard Enterprise Development LP
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import contextlib
import argparse
import re
import copy
from lxml import etree
from math import hypot
from datetime import datetime
import os
import sys
import syslog
from collections import namedtuple, OrderedDict
import zipfile
import uuid
from SortedCollection import SortedCollection
from pdb import set_trace, post_mortem
import traceback
from functools import total_ordering
from fuzzywuzzy import process as fuzzy_process
from bitstring import BitArray

VNS = 'http://schemas.microsoft.com/office/visio/2012/main'          # Visio
WNS = 'http://schemas.openxmlformats.org/wordprocessingml/2006/main' # Word
W14NS = 'http://schemas.microsoft.com/office/word/2010/wordml'       # Word14
XMLNS = 'http://www.w3.org/XML/1998/namespace'                       # XML
NSC = '{'+VNS+'}'
WNSC = '{'+WNS+'}'
W14NSC = '{'+W14NS+'}'
XMLNSC = '{'+XMLNS+'}'
NSMAP = { None : VNS }
VNSMAP = { 'v' : VNS, 'w' : WNS, 'xml' : XMLNS }  # for find, iterfind, xpath
#COLUMN_WIDTH = 1.1
COLUMN_WIDTH = 2.5
HALF = 0.5
QUARTER = 0.25
EIGHTH = 0.125
SIXTEENTH = 0.0625
NINETY_DEGREES = 1.571  # 90 degrees is 1.571 radians
VARIABLE = -41600
OS2 = -41777
NN = -41888
YY = -41999
UNKNOWN = -42000
offset_name = { OS2: 'OS2', NN : 'NN', YY : 'YY', UNKNOWN : 'UNKNOWN',
                VARIABLE : 'VARIABLE' }
EM_DASH = chr(0x2014)  # Unicode em-dash

keyboard = set_trace
re_field_match = re.compile('<name>(?P<head>[^\d<]+)'+
                            '((?P<wild><wild/>)|'+
                            '<sub>(?P<sub>[\w]+)</sub>|'+
                            '<ix>(?P<ix>[\w]+)</ix>)?'+
                            '[\s]*'+
                            '(?P<num>[\d]+)'+
                            '(?P<tail>[^\[]*)'+
                            '(?P<bits>\[.*\])?'+
                            '</name>')
re_fname_match = re.compile('<name>(?P<name>[^<\[]*)'+
                            '((?P<wild><wild/>)|'+
                            '<sub>(?P<sub>[\w]+)</sub>|'+
                            '<ix>(?P<ix>[\w]+)</ix>)?'+
                            '(?P<mid>[^\[<]*)'+
                            '((?P<wild2><wild/>)|'+
                            '<sub>(?P<sub2>[\w]+)</sub>|'+
                            '<ix>(?P<ix2>[\w]+)</ix>)?'+
                            '(?P<tail>[^\[]*)'+
                            '(?P<bits>\[.*\])?'+
                            '</name>')
re_range_match = re.compile('(Payload \[.*\] = )?'+
                            '(?P<name>[ \w\|-]+)'+
                            ' \[((?P<max>[N\d]+)(?P<sep>[:-]))?(?P<min>[\d]+)\]')
re_byte_match = re.compile('< Byte (?P<lo>0x[\dA-F]+) / (?P<hi>0x[\dA-F]+)')
re_ptr_match = re.compile('<name>.*PTR( \[.*\]| [\d]+|<sub>.*</sub>| <ix>.*</ix>)?</name>')
re_desc_ref2  = re.compile('[\s]+REF[\s]'+
                           '(?P<ref>_Ref[\d]+).*')

# Visio axes:
#
# y ^
#   |
#   |
#   +------> x

def canonical_name(txt):
    return ' '.join(txt.split())

def find(s, ch):
    return [i for i, ltr in enumerate(s) if ltr == ch]

class Shape():
    def __init__(self, shape, id, fname, parent=None):
        self.shape = shape
        self.id = id
        self.fname = fname
        self.parent = parent
        self.set_dimensions()

    def round(self, v):
        return round(float(v), 3)

    def reparent(self, parent):
        self.parent = parent

    def set_dimensions(self):
        p = self.parent
        found = 0
        for cell in self.shape.iterfind('v:Cell', namespaces=VNSMAP):
            n = cell.get('N')
            v = cell.get('V')
            if n == 'PinX':
                self.x = self.round(v) + (p.origin_x if p is not None else 0)
                found |= 0x1
            elif n == 'PinY':
                self.y = self.round(v) + (p.origin_y if p is not None else 0)
                found |= 0x2
            elif n == 'LocPinX':
                self.loc_x = self.round(v)
                found |= 0x4
            elif n == 'LocPinY':
                self.loc_y = self.round(v)
                found |= 0x8
            elif n == 'Width':
                width = self.round(v)
                found |= 0x10
            elif n == 'Height':
                height = self.round(v)
                found |= 0x20
            elif n == 'Angle':
                angle = self.round(v)
                found |= 0x40
            if found == 0x7f:
                break
        # end for cell

        if (found & 0x40) and (angle == NINETY_DEGREES):
            # height & width swapped
            self.w = height
            self.h = width
        else:
            self.w = width
            self.h = height
        
    @property
    def origin_x(self):
        return self.x - self.loc_x
        
    @property
    def origin_y(self):
        return self.y - self.loc_y

    @property
    def left_x(self):
        return self.x - (self.w * HALF)

    @property
    def right_x(self):
        return self.x + (self.w * HALF)

    def distance(self, other):
        return hypot(self.x-other.x, self.y-other.y)

    def below(self, other):  # is self below other
        return (self.y < other.y)

    def same_column(self, other):  # are self and other in "same column"
        return (abs(self.x - other.x) <= COLUMN_WIDTH)

    @property
    def name(self):
        return str(self.fname)

    def __repr__(self):
        return '{obj}(id={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), "{nm}")'.format(
            id=self.id, nm=self.fname, x=self.x, y=self.y, w=self.w, h=self.h,
            obj=type(self).__name__)

class Field(Shape):
    def __init__(self, shape, id, fname, parent=None):
        self.max_bit, self.min_bit = -2, -1  # out of range, and such that num_bits==0
        self.header, self.offset, self.value, self.mo = None, None, None, None
        self.access = None
        self.parent = parent
        self.subfields = []
        self.base_bit = 0
        self.vals = []
        self.ptr = None
        super().__init__(shape, id, fname, parent)

    def sort_key(self):
        return self.min_bit

    def add_subfield(self, sub):
        self.subfields.append(sub)

    @property
    def subfield_bits(self):
        return sum(sub.num_bits for sub in self.subfields)

    @property
    def num_bits(self):
        return self.max_bit - self.min_bit + 1

    @property
    def adj_min_bit(self):
        return self.base_bit

    @property
    def adj_max_bit(self):
        return self.base_bit + self.num_bits - 1

    @property
    def num_elems(self):
        if (self.parent is not None and isinstance(self.parent, Element) and
            self.parent.parent is not None and
            isinstance(self.parent.parent, Array)):
            return self.parent.parent.num_elems
        return None

    def find_header(self, headers):
        min_d = 100000
        min_h = None
        for h in headers:
            if self.below(h):
                d = self.distance(h)
                if d < min_d:
                    min_d = d
                    min_h = h
        self.header = min_h
        return min_h

    def find_offset(self, offsets):
        top_y = self.y + (self.h * HALF)
        bot_y = self.y - (self.h * HALF)
        best_o = None
        for o in offsets:
            if o.y < top_y and o.y > bot_y:
                if best_o is None or o.y > best_o.y:
                    best_o = o

        self.offset = best_o
        return best_o

    def set_max_bit(self):
        try:
            self.max_bit = self.header.bits.find_gt(self.left_x).bit
        except (ValueError, AttributeError):
            self.max_bit = UNKNOWN

    def set_min_bit(self):
        try:
            self.min_bit = self.header.bits.find_lt(self.right_x).bit
        except (ValueError, AttributeError):
            self.min_bit = UNKNOWN

    def set_base_bit(self):
        if self.fname.text[-1] == ']':
            scale = 1
            m = re_range_match.fullmatch(self.fname.text)
            try:
                sep = m.group('sep')
                if sep is not None:
                    scale = 8 if sep == '-' else 1
                    max = m.group('max')
                    if max == 'N':
                        max = UNKNOWN
                    else:
                        max = (int(max) * scale) + scale - 1
                min = int(m.group('min')) * scale
                self.base_bit = min
            except (ValueError, TypeError, AttributeError):
                print('Invalid bit range for "{}"'.format(self.name))

    def create_xml(self, parent):
        num_bits_valid = (self.num_bits > 0 and
                          self.min_bit >= 0 and self.max_bit >= 0)
        self.xml = etree.SubElement(parent, 'field',
                                    num_bits='{}'.format(self.num_bits
                                                         if num_bits_valid
                                                         else 'UNKNOWN'),
                                    min_bit='{}'.format(self.min_bit
                                                        if self.min_bit >= 0
                                                        else 'UNKNOWN'),
                                    max_bit='{}'.format(self.max_bit
                                                        if self.max_bit >= 0
                                                        else 'UNKNOWN'))
        if args.ids:
            self.xml.set('id', self.id)
        self.xml.append(copy.deepcopy(self.fname.tree))
        if self.value is not None:
            self.xml.set('value', '{:#x}'.format(self.value))
        if self.mo:
            self.xml.set('mo', self.mo)
        if self.access:
            self.xml.set('access', self.access)
        if self.base_bit != 0:
            self.xml.set('base_bit', '{}'.format(self.base_bit))
        if self.ptr is not None:
            tgt = (self.ptr.target.name if self.ptr.target is not None
                   else 'UNKNOWN')
            self.xml.set('ptr_to', tgt)
        for val in self.vals:
            val.create_xml(self.xml)
        for sub in self.subfields:
            sub.create_xml(self.xml)

    def __repr__(self):
        return '{obj}(id={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), "{nm}", {{{max}:{min}}})'.format(
            id=self.id, nm=self.fname, x=self.x, y=self.y, w=self.w, h=self.h,
            obj=type(self).__name__, max=self.max_bit, min=self.min_bit)

class Dot3(Field):
    def __init__(self, shape, id, fname, parent=None):
        self.dot3 = True
        super().__init__(shape, id, fname, parent)

    def siblings(self):
        return [c for c in self.parent.group if c is not self] if self.parent else None

class Bit(Shape):
    def __init__(self, shape, id, fname, byte=None, parent=None):
        try:
            self.bit = int(fname.text)
        except ValueError:
            self.bit = UNKNOWN
        self.byte = byte
        if byte is not None:
            self.set_byte(byte)
        super().__init__(shape, id, fname, parent)

    def sort_key(self):
        return self.x

    def closest_byte(self, bytes):
        min_d = 100000
        min_b = None
        for b in bytes:
            if self.below(b):
                d = self.distance(b)
                if d < min_d:
                    min_d = d
                    min_b = b
        return min_b

    def set_byte(self, b):
        self.byte = b
        self.bit += (8 * b.byte)

    def __repr__(self):
        return super().__repr__()[:-1] + ', bit={bit})'.format(bit=self.bit)

class Byte(Shape):
    def __init__(self, shape, id, fname, parent=None):
        self.byte = int(fname.text[1:])
        super().__init__(shape, id, fname, parent)

@total_ordering
class Offset(Shape):
    def __init__(self, shape, id, fname, parent=None):
        name = fname.text
        self.offset_pair = None
        try:
            self.offset = int(name[7:], base=0)
        except ValueError:
            if len(name) > 8 and name[7:9] == 'NN':
                self.offset = NN
            elif len(name) > 10 and name[7:11] == '0xNN':
                self.offset = NN
            elif len(name) > 8 and name[7:9] == 'YY':
                self.offset = YY
            elif len(name) > 10 and name[7:11] == '0xYY':
                self.offset = YY
            elif len(name) > 9 and name[7:10] == 'OS2':
                self.offset = OS2
            else:
                m = re_byte_match.fullmatch(name)
                if m:
                    lo = int(m.group('lo'), base=0)
                    hi = int(m.group('hi'), base=0)
                    self.offset_pair = (lo, hi)
                    self.offset = hi  # for offset_pair-unaware code
                else:
                    self.offset = UNKNOWN
        self.fields = SortedCollection(key=Field.sort_key)
        self.num_bits = 0
        super().__init__(shape, id, fname, parent)

    def __eq__(self, other):
        if not self._is_valid_operand(other):
            return NotImplemented
        return self.sort_key() == other.sort_key()

    def __lt__(self, other):
        if not self._is_valid_operand(other):
            return NotImplemented
        return self.sort_key() < other.sort_key()

    def _is_valid_operand(self, other):
        return hasattr(other, 'sort_key')

    def sort_key(self):
        return abs(self.offset)  # abs forces NN, YY, UNKNOWN to end

    def add_field(self, field):
        self.fields.insert(field)
        self.num_bits = max(self.num_bits, field.max_bit + 1)

    @property
    def bytes(self):
        return self.num_bits // 8

    def create_xml(self, parent):
        if self.offset_pair is not None:
            val = '{:#x} | {:#x}'.format(self.offset_pair[0],
                                         self.offset_pair[1])
        else:
            val = ('{:#x}'.format(self.offset) if self.offset >= 0 else
                   offset_name[self.offset])
        self.xml = etree.SubElement(parent, 'offset', value=val, num_bits='{}'.
                                    format(self.num_bits))
        if args.ids:
            self.xml.set('id', self.id)
        for f in self.fields:
            f.create_xml(self.xml)

class Pointer(Shape):
    def __init__(self, shape, id, fname, parent=None):
        self.ptr = fname.text[3:]
        super().__init__(shape, id, fname, parent)

    def sort_key(self):
        return self.ptr

class Index(Shape):
    def __init__(self, shape, id, fname, parent=None):
        self.index = fname.text[:-2]
        super().__init__(shape, id, fname, parent)

    def sort_key(self):
        return self.index

class Group(Shape):
    def __init__(self, shape, id, group, fname=None, level=0, parent=None):
        self.group = group
        self.level = level
        self.fields_by_name = {}
        self.fixup_headers = False
        super().__init__(shape, id, fname, parent)

    def remove(self, obj, stop=None):
        vprint('{} ignoring remove of {}'.format(self, obj), min=1)
        return False

    def setup_headers(self, first=False):
        hdrs = self.find_instances(Header)
        if self.parent is not None:
            hdrs += self.parent.setup_headers()
        return hdrs

    def setup_instances(self):
        self.headers = self.setup_headers(first=True)
        # Revisit: workaround for Group/Header ordering
        if len(self.headers) == 0:
            self.fixup_headers = True
        self.offsets = self.find_instances(Offset)
        self.fields = self.find_instances(Field)
        self.pointers = self.find_instances(Pointer)
        self.arrays = self.find_instances(Array, recurse=False)
        self.all_arrays = self.find_instances(Array, array_recurse=True)

    def find_instances(self, instance, recurse=True, array_recurse=False):
        instances = []
        try:
            for g in self.group:
                if isinstance(g, instance):
                    instances.append(g)
                if ((recurse and isinstance(g, Group)) and
                      (not isinstance(g, Array) or array_recurse)):  # recurse
                    instances.extend(g.find_instances(instance,
                                                      recurse, array_recurse))
        except TypeError:  # a "fake" group is not iterable
            if isinstance(self.group, instance):
                instances.append(self.group)
        return sorted(instances, key=instance.sort_key)

    def setup_fields(self):
        # Revisit: workaround for Group/Header ordering
        if self.fixup_headers:
            self.headers = self.setup_headers(first=True)
            self.fixup_headers = False
            if len(self.headers) > 0:
                vprint('{} fixup hdrs={}'.format(self, self.headers), min=1)
        try:
            for f in self.fields:
                self.fields_by_name[f.name] = f
                h = f.find_header(self.headers)
                o = f.find_offset(self.offsets)
                f.set_max_bit()
                f.set_min_bit()
                f.set_base_bit()
                if o is not None:
                    o.add_field(f)
                vprint('{}: header={}, offset={}'.format(
                    f, h.id if h is not None else 'UNKNOWN',
                    o.name if o is not None else 'UNKNOWN'), min=1)
        except AttributeError:
            print('Invalid Group: {} has no fields'.format(self))
        remove = []
        try:
            for a in self.arrays:
                vprint('{} calling setup_fields for {}'.format(self, a), min=2)
                a_off, a_remove = a.setup_fields()
                remove.extend(a_remove)
        except AttributeError:
            print('Invalid Group: {} has no arrays'.format(self))
        return (None, remove)

    def field_by_name(self, name):
        if isinstance(name, FieldName):
            return self.fields_by_name[name.name]
        else:  # assume str
            return self.fields_by_name[FieldName(name=name).name]

    def match_field_name(self, fname):
        return filter(lambda f: self.match_field_names(f, fname),
                      self.fields)

    def match_field_names(self, f, fname):
        # match field names ignoring subscripts/indexes/bit-ranges/wildcards
        # Format:  head(<sub>|<ix>|<wild>)?mid(<sub2><ix2><wild2>)?tail[bits]?
        # See re_fname_match for details
        # f is from the Structure, fname is from the table
        flen = len(f.name)
        fnamelen = len(fname.name)
        # Initially, head/tail are both entire string excluding '</name>'
        f_start_end = ( [0, flen-7], [0, flen-7] )
        fname_start_end = ( [0, fnamelen-7], [0, fnamelen-7] )
        m_f = re_fname_match.fullmatch(f.name)
        m_fname = re_fname_match.fullmatch(fname.name)
        f_sub = False
        if m_f is not None:
            if m_f.group('bits'):
                # Move end of head & tail left
                f_start_end[0][1] = min(m_f.start('bits') - 1,
                                        f_start_end[0][1])
                f_start_end[1][1] = min(m_f.start('bits') - 1,
                                        f_start_end[1][1])
            if m_f.group('sub'):
                # Move end of head left, start of tail right
                f_start_end[0][1] = min(m_f.start('sub') - 5,
                                        f_start_end[0][1])
                f_start_end[1][0] = max(m_f.end('sub') + 6,
                                        f_start_end[1][0])
                f_sub = True
        if m_fname is not None:
            if m_fname.group('wild'):
                # Wild only allowed with [bits], not with <sub> and/or <ix>
                re_wild = fname.name.replace('<wild/>', '.*')
                re_wild = re_wild.replace('</name>', '( \[.*\])?</name>')
                if re.match(re_wild, f.name):
                    vprint('wild match: "{}" "{}"'.format(
                        fname.name, f.name), min=2)
                    return True
            if m_fname.group('ix') or m_fname.group('ix2'):
                # Move end of head left, start of tail right
                tag = 'ix' if m_fname.group('ix') else 'ix2'
                fname_start_end[0][1] = min(m_fname.start(tag) - 4,
                                            fname_start_end[0][1])
                fname_start_end[1][0] = max(m_fname.end(tag) + 5,
                                            fname_start_end[1][0])
                m_field = re_field_match.match(f.name)
                if m_field is not None:
                    # Move end of head left, start of tail right
                    f_start_end[0][1] = min(m_field.start('num'),
                                            f_start_end[0][1])
                    f_start_end[1][0] = max(m_field.end('num'),
                                            f_start_end[1][0])
            if m_fname.group('sub'):
                # Move end of head left, start of tail right
                fname_start_end[0][1] = min(m_fname.start('sub') - 5,
                                            fname_start_end[0][1])
                fname_start_end[1][0] = max(m_fname.end('sub') + 6,
                                            fname_start_end[1][0])
            else:
                if f_sub:  # special case: match against field with <sub>
                    fname_start_end[1][0] = fnamelen
                    fname_start_end[1][1] = fnamelen
        f_head = f.name[f_start_end[0][0]:f_start_end[0][1]]
        f_tail = f.name[f_start_end[1][0]:f_start_end[1][1]]
        fname_head = fname.name[fname_start_end[0][0]:fname_start_end[0][1]]
        fname_tail = fname.name[fname_start_end[1][0]:fname_start_end[1][1]]
        return f_head == fname_head and f_tail == fname_tail

@total_ordering
class Array(Group):
    def __init__(self, shape, id, group, fname=None, level=0, parent=None,
                 dots=None):
        self.offset = UNKNOWN
        self.offset_pair = None
        self.num_elems = UNKNOWN
        self.siblings = dots.siblings()
        self.elements = []
        group.remove(dots)
        super().__init__(shape, id, group, fname, level, parent)
        try:
            for g in group:
                g.reparent(self)
        except TypeError:
            vprint('TypeError in {} due to group {} not iterable'.format(
                self, group))
            pass
        for sib in self.siblings:
            group.remove(sib)
            elem = Element(sib.shape, sib.id,
                           sib.group if isinstance(sib, Group) else sib,
                           fname, level, parent=self)
            self.elements.append(elem)

    def __eq__(self, other):
        if not self._is_valid_operand(other):
            return NotImplemented
        return self.sort_key() == other.sort_key()

    def __lt__(self, other):
        if not self._is_valid_operand(other):
            return NotImplemented
        return self.sort_key() < other.sort_key()

    def _is_valid_operand(self, other):
        return hasattr(other, 'sort_key')

    def sort_key(self):
        return abs(self.offset)  # abs forces YY, UNKNOWN, VARIABLE to end

    def setup_instances(self):
        for e in self.elements:
            e.setup_instances()

    def setup_fields(self):
        min_off = abs(UNKNOWN)
        max_off = UNKNOWN
        yy_nn_off = None
        remove = []
        for e in self.elements:
            vprint('{} calling setup_fields for {}'.format(self, e), min=2)
            off, e_remove = e.setup_fields()
            remove.extend(e_remove)
            if self.offset_pair is None and e.offset_pair is not None:
                self.offset_pair = e.offset_pair
            if off == UNKNOWN:
                if e.bytes == 0 or e.bytes == UNKNOWN:
                    self.num_elems = VARIABLE
                    vprint('{} removing {} due to UNKNOWN'.format(
                        self, e), min=1)
                    remove.append((self, e))
            elif off == YY or off == NN:
                self.num_elems = VARIABLE
                yy_nn_off = off
                vprint('{} removing {} due to YY/NN'.format(self, e), min=1)
                remove.append((self, e))
            else:
                min_off = min(min_off, off)
                max_off = max(max_off, off)
        # end for e
        self.offset = (min_off if min_off != abs(UNKNOWN) else
                       (yy_nn_off if yy_nn_off is not None else UNKNOWN))
        vprint('{} setting offset={}'.format(self, self.offset), min=2)
        if (min_off >= 0 and min_off < abs(UNKNOWN) and
            max_off >= 0 and self.num_elems != VARIABLE) : # fixed-size array
            elem_size = self.elements[0].bytes
            try:
                self.num_elems = ((max_off - min_off) // elem_size) + 1
            except ZeroDivisionError:
                print('Array {} has zero-size Element'.format(self))
        return (self.offset, remove)

    def remove(self, elem, stop=None):
        vprint('{} remove of {}'.format(self, elem), min=1)
        try:
            self.elements.remove(elem)
        except ValueError:
            vprint('{} already removed {}'.format(self, elem), min=1)
            return
        empty = self.is_empty()
        if empty:
            vprint('{} is_empty after remove of {}'.format(self, elem), min=1)
        return empty

    def is_empty(self):
        return not self.elements

    def find_instances(self, instance, recurse=True, array_recurse=False):
        instances = []
        if recurse and array_recurse:
            for e in self.elements:
                instances.extend(e.find_instances(instance,
                                                  recurse, array_recurse))
        return sorted(instances, key=instance.sort_key)

    def match_field_name(self, fname):
        m = tuple()
        for e in self.elements:
            m += tuple(e.match_field_name(fname))
        return m

    def create_xml(self, parent):
        if self.offset_pair is not None:
            off = '{:#x} | {:#x}'.format(self.offset_pair[0],
                                         self.offset_pair[1])
        else:
            off = ('{:#x}'.format(self.offset) if self.offset >= 0 else
                   offset_name[self.offset])
        elems = ('{}'.format(self.num_elems) if self.num_elems >= 0 else
                 offset_name[self.num_elems])
        bytes = ('{:#x}'.format(self.bytes) if self.bytes >= 0 else
                 offset_name[self.bytes])
        self.xml = etree.SubElement(parent, 'array', offset=off,
                                    elements=elems, bytes=bytes)
        if args.ids:
            self.xml.set('id', self.id)
        for e in self.elements:
            e.create_xml(self.xml)

    @property
    def bytes(self):
        if self.num_elems == VARIABLE:
            return VARIABLE
        if not self.elements:
            return UNKNOWN
        for e in self.elements:
            b = e.bytes
            if b == VARIABLE:
                return VARIABLE
        return self.num_elems * b

class Element(Group):
    def __init__(self, shape, id, group, fname=None, level=0, parent=None):
        self.array = parent
        self.offset = UNKNOWN
        self.offset_pair = None
        self.bytes = UNKNOWN
        super().__init__(shape, id, group, fname, level, parent)
        try:
            for g in group:
                g.reparent(self)
        except TypeError:
            vprint('TypeError in {} due to group {} not iterable'.format(
                self, group))
            pass

    def setup_fields(self):
        _, remove = super().setup_fields()
        min_off = abs(UNKNOWN)
        max_off = UNKNOWN
        bytes = 0
        try:
            for o in self.offsets:
                if self.offset_pair is None and o.offset_pair is not None:
                    self.offset_pair = o.offset_pair
                if o.offset == YY:
                    if o.num_bits == 0:
                        vprint('{} removing {} due to num_bits'.format(
                            self, o), min=1)
                        remove.append((self, o))
                    self.offset = YY
                    continue
                min_off = min(min_off, o.offset)
                max_off = max(max_off, o.offset)
                bytes += o.bytes
            for a in self.arrays:
                if a.offset == YY:
                    self.offset = YY
                    continue
                min_off = min(min_off, a.offset)
                max_off = max(max_off, a.offset)
                if a.num_elems == VARIABLE:
                    self.bytes = VARIABLE
                else:
                    bytes += a.bytes
        except AttributeError:
            print('Invalid array element: {}'.format(self.group))
        if self.offset != YY and min_off < abs(UNKNOWN):
            self.offset = min_off
            vprint('{} setting offset={}'.format(self, self.offset), min=2)
        if self.bytes == UNKNOWN and bytes >= 0:
            self.bytes = bytes
        return (self.offset, remove)

    def remove(self, obj, stop=None):
        vprint('{} remove of {}'.format(self, obj), min=1)
        if obj in self.offsets:
            self.offsets.remove(obj)
        elif obj in self.arrays:
            self.arrays.remove(obj)
        empty = self.is_empty()
        if empty:
            vprint('{} is_empty after remove of {}'.format(self, obj), min=1)
        return empty

    def is_empty(self):
        return not self.offsets and not self.arrays

    def sort_key(self):
        return abs(self.offset)  # abs forces NN, YY, UNKNOWN to end

    def create_xml(self, parent):
        if self.offset_pair is not None:
            off = '{:#x} | {:#x}'.format(self.offset_pair[0],
                                         self.offset_pair[1])
        else:
            off = ('{:#x}'.format(self.offset) if self.offset >= 0 else
                   offset_name[self.offset])
        by  = '{:#x}'.format(self.bytes) if self.bytes >= 0 else offset_name[self.bytes]
        self.xml = etree.SubElement(parent, 'element', offset=off, bytes=by)
        if args.ids:
            self.xml.set('id', self.id)
        try:
            for child in sorted(self.offsets + self.arrays):
                child.create_xml(self.xml)
        except AttributeError:
            print('Invalid array element: {}'.format(self.group))

class Header(Group):
    def __init__(self, shape, id, group, bits, bytes, level=0, parent=None):
        self.bytes = bytes
        if len(bits) == 0:
            bits = self.fake_bits(level+1)
        self.bits = SortedCollection(bits, key=Bit.sort_key)
        self.min_bit = 10000
        self.max_bit = -10000
        for b in bits:
            self.min_bit = min(self.min_bit, b.bit)
            self.max_bit = max(self.max_bit, b.bit)
        super().__init__(shape, id, group, level=level, parent=parent)

    def sort_key(self):
        return self.min_bit  # really a don't care

    def fake_bits(self, level):  # create "fake" bits for all the bytes
        bits = []
        by_count = len(self.bytes)
        hdr_width = self.bytes[0].parent.w
        for by in self.bytes:
            by_w = hdr_width / by_count
            vprint('{pad: <{ind}}{obj:6s}: '.format(
                obj=by.__class__.__name__, ind=2*level+2, pad=' ') +
                   'ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), '.format(
                       id=by.id, x=by.x, y=by.y, w=by.w, h=by.h) +
                   '"{nm}" fake'.format(nm=by.name), min=2)
            width = by_w * EIGHTH
            half_width = by_w * SIXTEENTH

            by_pinx = by.x - by.parent.origin_x
            for bit_num in range(8):
                pinx = by_pinx + (by_w * HALF) - (bit_num * width) - half_width
                id = 'Fake{}'.format(bit_num)
                name = '{}'.format(bit_num)
                fname = FieldName(name=name)
                shape = self.fake_shape(id, name, pinx, width, by.shape.getparent())
                b = Bit(shape, id, fname, byte=by, parent=by.parent)
                bits.append(b)
                vprint('{pad: <{ind}}{obj:6s}: '.format(
                    obj=b.__class__.__name__, ind=2*(level+1)+2, pad=' ') +
                       'ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), '.format(
                           id=b.id, x=b.x, y=b.y, w=b.w, h=b.h) +
                       '"{nm}" fake'.format(nm=b.name), min=2)
            # end for bit_num
        # end for by
        return bits

    def fake_shape(self, id, name, pinx, width, parent):  # create a "fake" XML shape
        shape = etree.SubElement(parent, NSC+'Shape', Type='Shape', ID=id)
        etree.SubElement(shape, NSC+'Cell', V='{:.3f}'.format(pinx), N='PinX')
        etree.SubElement(shape, NSC+'Cell', V='0.106', N='PinY')
        etree.SubElement(shape, NSC+'Cell', V='{:.3f}'.format(width), N='Width')
        etree.SubElement(shape, NSC+'Cell', V='0.064', N='Height')
        etree.SubElement(shape, NSC+'Cell', V='{:.3f}'.format(width/2), N='LocPinX')
        etree.SubElement(shape, NSC+'Cell', V='0.032', N='LocPinY')
        txt = etree.SubElement(shape, NSC+'Text')
        txt.text = name
        return shape

    @property
    def num_bits(self):
        return self.max_bit - self.min_bit + 1

class PTR():
    def __init__(self, fld, fname, ref):
        self.field = fld
        self.fname = fname
        self.ref = ref
        self.target = None

    def link_PTR(self, word):
        if self.fname.name == word.generic_fname.name:
            self.target = word.generic_struct
            vprint('PTR: {} points to {} via generic_struct'.format(
                self.fname.name, self.target), min=2)
            return
        try:
            s = word.struct_by_ptr(self.fname.text)
            self.target = s
            vprint('PTR: {} points to {} via struct_by_ptr'.format(
                self.fname.name, self.target), min=2)
            return
        except KeyError:
            pass
        if self.ref is None:
            return
        sect, table = self.ref
        if table is None:
            table = sect.table_match(self.fname.text)
            vprint('PTR: "{}" fuzzy matched to {}'.format(
                self.fname.text, table), min=1)
        txt = table.title.text
        m = word.re_fields_tbl.match(txt)
        if m:
            name = m.group('name')
            vprint('PTR: {} xref to Field {}, name="{}"'.format(
                self.fname.name, table, name), min=2)
            try:
                s = word.struct_by_name(name)
            except KeyError:
                vprint('PTR: {} not found'.format(name), min=1)
                return
            self.target = s
            vprint('PTR: {} points to {} via xref'.format(
                self.fname.name, self.target), min=1)
        else:
            print('PTR: {} has invalid Field Table reference'.format(
                self.fname.name))

class Subfield():
    def  __init__(self, loc, access, fname, vals, desc=None, mo=None):
        if len(loc.text) > 3 and loc.text[0:3] == 'Bit':
            st = 4
        else:
            st = 0
        colon = loc.text.find(':', st)
        try:
            if colon >= 0:
                self.min_bit = int(loc.text[colon+1:])
                self.max_bit = int(loc.text[st:colon])
            else:
                self.min_bit = int(loc.text[st:])
                self.max_bit = self.min_bit
        except ValueError:
            print('Invalid bit location "{}" for "{}"'.format(
                loc, fname))
            self.min_bit = -1
            self.max_bit = -1
        if self.min_bit > self.max_bit:
            print('Reversed bit location range "{}" for "{}"'.format(
                loc, fname))
        self.fname = fname
        self.vals = vals
        self.access = access if access != '' else None
        self.mo = mo if mo is not None and mo != '' else None

    @property
    def num_bits(self):
        return self.max_bit - self.min_bit + 1

    def within(self, field):
        if (self.min_bit >= field.adj_min_bit and
            self.max_bit <= field.adj_max_bit):
            return True
        return False

    def create_xml(self, parent):
        self.xml = etree.SubElement(parent, 'subfield',
                                    min_bit='{}'.format(self.min_bit),
                                    max_bit='{}'.format(self.max_bit),
                                    num_bits='{}'.format(self.num_bits))
        if self.access:
            self.xml.set('access', self.access)
        if self.mo:
            self.xml.set('mo', self.mo)
        if self.fname is not None:
            self.xml.append(copy.deepcopy(self.fname.tree))
        if self.vals is not None:
            for val in self.vals:
                val.create_xml(self.xml)

class Para():
    def __init__(self, para=None, tc=None, txt=None, ref=False):
        self.paraId = None
        self.tree = etree.Element('para')
        if para is not None:
            self.parse_para_text(para, ref=ref)
        elif tc is not None:
            self.parse_para_text(tc.find('w:p', namespaces=VNSMAP))
        elif txt is not None:
            self.text = txt

    def __repr__(self):
        return etree.tostring(self.tree, encoding='unicode')

    @property
    def name(self):
        return repr(self)

    @property
    def text(self):
        return self._text

    @text.setter
    def text(self, val):
        self._text = val
        self.tree.text = val

    def parse_para_text(self, para, ref=False):
        self._text, self._ref = get_para_text(para, self.tree, ref=ref)
        self.paraId = para.get(W14NSC+'paraId')

class FieldName():
    def __init__(self, para=None, shape=None, name=None, xml=None, split=None):
        self.tree = etree.Element('name')
        if para is not None:
            self.parse_para_text(para, split)
        elif shape is not None:
            self.parse_shape_text(shape)
        elif xml is not None:
            self.tree = etree.XML(xml)
            self._text = get_text(self.tree)
        elif name is not None:
            self.text = name

    def __repr__(self):
        return etree.tostring(self.tree, encoding='unicode')

    @property
    def name(self):
        return repr(self)

    @property
    def text(self):
        return self._text

    @text.setter
    def text(self, val):
        self._text = val
        self.tree.text = val

    def parse_para_text(self, para, split):
        self._text, self._ref = get_para_text(para, self.tree, split)

    def parse_shape_text(self, shape):
        field_txt = ''
        e = self.tree
        e.text = ''
        tail = False
        next_tail = False
        no_txt = True
        text = shape.find('v:Text', namespaces=VNSMAP)
        if text is None:
            return
        # Revist: this is pretty slow
        sub, sup = self.sub_sup_indexes(shape)
        for child in text.iter(NSC+'cp', NSC+'pp', NSC+'tp'):
            if next_tail:
                tail = True
            trailing_newline = False
            ix = int(child.get('IX'))
            if child.tag == NSC+'pp' or child.tag == NSC+'tp':
                tail = False
                next_tail = not no_txt
            elif ix in sub:
                tail = False
                next_tail = True
                e = etree.SubElement(self.tree, 'sub')
                e.text = ''
            elif ix in sup:
                tail = False
                next_tail = True
                e = etree.SubElement(self.tree, 'sup')
                e.text = ''
            else:
                next_tail = False
            if child.tail is not None and child.tail[-1] == '\n':
                trailing_newline = True
            txt = child.tail.replace('\n', ' ') if child.tail is not None else ''
            txt = txt.replace('\u2028', ' ') # unicode line-separator
            if tail:
                if e.tail:
                    e.tail += txt
                else:
                    e.tail = txt
            else:
                e.text += txt
                no_txt = len(e.text) == 0
            field_txt += txt
        #end for child
        if trailing_newline:
            if tail:
                e.tail = e.tail.rstrip()
            else:
                e.text = e.text.rstrip()
        self._text = field_txt.strip()

    def sub_sup_indexes(self, shape):
        sub = []
        sup = []
        char_sect = self.find_character_section(shape)
        rows = char_sect.findall('v:Row', namespaces=VNSMAP)
        for row in rows:
            ix = int(row.get('IX'))
            pos = self.find_pos_cell(row)
            if pos is not None:
                val = int(pos.get('V'))
                if val == 1:
                    sup.append(ix)
                elif val == 2:
                    sub.append(ix)
        # end for row
        return (sub, sup)

    def find_character_section(self, shape):
        sections = shape.findall('v:Section', namespaces=VNSMAP)
        for s in sections:
            if s.get('N') == 'Character':
                return s
        return None

    def find_pos_cell(self, row):
        cells = row.findall('v:Cell', namespaces=VNSMAP)
        for cell in cells:
            if cell.get('N') == 'Pos':
                return cell
        return None

class FieldVal():
    def __init__(self, m):
        self.val = m.group('val')
        self.min_val = m.group('min')
        self.max_val = m.group('max')
        self.fname = FieldName(xml='<name>'+m.group('name')+'</name>')
        self.other = m.group('other')

    def create_xml(self, parent):
        self.xml = etree.SubElement(parent, 'value')
        self.xml.append(copy.deepcopy(self.fname.tree))
        if self.val:
            self.xml.set('val', self.val)
        if self.min_val:
            self.xml.set('min_val', self.min_val)
        if self.max_val:
            self.xml.set('max_val', self.max_val)

class ComponentClass():
    def __init__(self, val, name):
        self.value = val
        self.name = name

    def create_xml(self, parent):
        self.xml = etree.SubElement(parent, 'class',
                                    value='{}'.format(self.value))
        self.xml.text = self.name

class DefinedUuid():
    def __init__(self, name, uuid, kind):
        self.name = name
        self.uuid = uuid
        self.kind = kind

    def create_xml(self, parent):
        self.xml = etree.SubElement(parent, 'uuid',
                                    value='{}'.format(self.uuid),
                                    kind=self.kind)
        self.xml.text = self.name

class Structure():
    generic = FieldName(name='Generic Structure')

    def __init__(self, kind, tag, zipinfo, shapes=[]):
        self.kind = kind
        self.tag = tag
        self.zipinfo = zipinfo
        self.shapes = shapes
        self.group = None
        self.type = UNKNOWN
        self.vers = UNKNOWN
        self.size = UNKNOWN
        self.min_size = UNKNOWN
        self.ptr = None
        self.PTRs = []

    def __repr__(self):
        kind = self.kind.fname if self.kind is not None else Structure.generic
        return '{obj}({kind})'.format(kind=kind.text, obj=type(self).__name__)

    def set_type(self, type):
        self.type = type
        self.tag = 'struct'

    def set_vers(self, vers):
        self.vers = vers

    def set_ptr(self, ptr):
        self.ptr = ptr

    def set_size(self):
        size = 0
        for o in self.group.offsets:
            b = o.bytes
            if o.offset < 0 or b < 0:
                self.size = VARIABLE
                self.min_size = round_up_n(size, 16)
                return
            size += b
        for a in self.group.arrays:
            b = a.bytes
            if b < 0:
                self.size = VARIABLE
                self.min_size = round_up_n(size, 16)
                return
            size += b
        self.size = size
        try:
            sz = self.field_by_name('Size')
            sz.value = size
        except KeyError:
            pass

    def sort_key(self):
        # sort 'struct' first, by type, then 'table', by name
        return self.tag + ('{:04x}'.format(self.type) if self.tag == 'struct'
                           else self.name)

    def field_by_name(self, name):  # returns single exact match
        return self.group.field_by_name(name)

    def match_field_name(self, fname):  # returns list of partial matches
        m = tuple(self.group.match_field_name(fname))
        try:
            for a in self.group.all_arrays:
                m += tuple(a.match_field_name(fname))
        except AttributeError:
            pass
        return m

    def find_group(self, groups):
        vprint('find_group({})'.format(self.kind), min=1)
        min_d = 100000
        min_g = None
        for g in groups:
            if args.verbose > 1:
                print('  checking {}'.format(g), end=':')
            try:
                if g.below(self.kind) and g.same_column(self.kind):
                    d = self.kind.distance(g)
                    if d < min_d:
                        vprint(' candidate, d={:.3f} < min_d={:.3f}'.format(d, min_d), min=1)
                        min_d = d
                        min_g = g
                    elif args.verbose > 1:
                        print(' not closest, d={:.3f}, min_d={:.3f}'.format(d, min_d))
                elif args.verbose > 1:
                    print(' not below({}) or not same_column({})'.format(
                        not g.below(self.kind), not g.same_column(self.kind)))
            except AttributeError as e:
                print(' find_group({}) AttributeError({}) for {} '.format(self, e, g))
        self.group = min_g
        return self.group

    def link_PTRs(self, word):
        for ptr in self.PTRs:
            ptr.link_PTR(word)

    @property
    def name(self):
        kind = self.kind.fname if self.kind is not None else Structure.generic
        return kind.text

    def create_xml(self, parent):
        try:
            self.xml = etree.SubElement(parent, self.tag, name=self.name)
        except AttributeError:
            print('create_xml failure on {}'.format(self.zipinfo.filename))
            return
        sz = '{:#x}'.format(self.size) if self.size >= 0 else offset_name[self.size]
        if self.type != UNKNOWN:
            self.xml.set('type', '{:#x}'.format(self.type))
        if self.vers != UNKNOWN:
            self.xml.set('vers', '{:#x}'.format(self.vers))
        if self.size != UNKNOWN:
            self.xml.set('size', sz)
        if self.size == VARIABLE and self.min_size >= 0:
            self.xml.set('min_size', '{:#x}'.format(self.min_size))
        if self.ptr is not None:
            self.xml.set('ptr', '{}'.format(' | '.join(self.ptr)))
        if self.group is None:
            print('{} has no offsets'.format(self))
        else:
            if args.ids:
                self.xml.set('id', self.group.id)
            try:
                for child in sorted(self.group.offsets + self.group.arrays):
                    child.create_xml(self.xml)
            except AttributeError:
                print('Invalid {} in {}'.format(self.group, self))

class Visio():
    re_visio_pages = re.compile('visio/pages/page[0-9]*.xml')

    def __init__(self, filename, tag):
        self.filename = filename
        self.tag = tag
        self.members = OrderedDict()
        self.trees = []
        with zipfile.ZipFile(filename, 'r') as self.zip:
            zipinfo = self.zip.infolist()

            for inf in filter(self.match_visio_pages, zipinfo):
                self.process_visio_page(inf)

    def __iter__(self):
        for m in self.members.values():
            yield m

    def __getitem__(self, key):
        return self.members[key]

    def match_visio_pages(self, zipinfo):
        return Visio.re_visio_pages.match(zipinfo.filename)

    def process_visio_page(self, zipinfo):
        vprint('{}:{}'.format(self.filename, zipinfo.filename))
        with self.zip.open(zipinfo) as f:
            tree = etree.parse(f)
            self.trees.append(tree)
            root = tree.getroot()
            vprint('root={}'.format(root.tag), min=2)
            structs = []
            groups = []
            for child in root:
                vprint('child={}'.format(child.tag), min=2)
                if child.tag == NSC+'Connects':
                    continue
                for shape in child:
                    vprint('shape={}'.format(shape.tag), min=2)
                    s = self.process_visio_shape(shape)
                    type = shape.get('Type')
                    if type == 'Shape':
                        struct = Structure(s, self.tag, zipinfo)
                        structs.append(struct)
                        self.members[struct.kind.fname.text] = struct
                    else:
                        groups.append(s)
                # end for shape
            # end for child
            for s in structs:
                if s.find_group(groups) is not None:
                    vprint('{} calling setup_fields for {}'.format(
                        s, s.group), min=2)
                    s_off, s_remove = s.group.setup_fields()
                    for o, r in s_remove:
                        done = False
                        while not done:
                            empty = o.remove(r)
                            if empty and o.parent is not None:
                                r = o
                                o = o.parent
                            else:
                                done = True
                else:
                    print('No group found for {}'.format(s))
            # end for s

    def process_visio_shape(self, shape, level=0, parent=None):
        type = shape.get('Type')
        id = shape.get('ID')
        pr = False
        if type == 'Shape':
            fname = FieldName(shape=shape)
            try:
                name = fname.text
            except AttributeError:  # shape has no Text
                return None
            if len(name) == 0:
                return None
            if name[0] == '+':
                obj = Byte(shape, id, fname, parent)
                pr = True
            elif name[0:7] == '< Byte ':
                obj = Offset(shape, id, fname, parent)
                pr = True
            elif name[0:3] == '<- ':
                obj = Pointer(shape, id, fname, parent)
                pr = True
            elif name[-2:] == ' >':
                obj = Index(shape, id, fname, parent)
                pr = True
            elif len(name) == 1 and name[0].isdigit():
                obj = Bit(shape, id, fname, parent=parent)
            elif name == '...':
                obj = Dot3(shape, id, fname, parent)
                vprint('{pad: <{ind}}{obj:5s}: ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), {sibs}'.
                       format(
                           id=id, sibs=[s.id for s in obj.siblings()],
                           x=obj.x, y=obj.y, w=obj.w, h=obj.h,
                           obj=obj.__class__.__name__, ind=2*level+2, pad=' '))
            else:
                obj = Field(shape, id, fname, parent)
                pr = True
            if pr:
                vprint('{pad: <{ind}}{obj:5s}: ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), "{nm}"'.
                       format(
                           id=id, nm=fname, x=obj.x, y=obj.y, w=obj.w, h=obj.h,
                           obj=obj.__class__.__name__, ind=2*level+2, pad=' '))
            return obj
        elif type == 'Group':
            group = []
            grp = Group(shape, id, group, level=level, parent=parent)
            vprint('{pad: <{ind}}Group: ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), level={lvl}'.
                   format(
                       id=id, x=grp.x, y=grp.y, w=grp.w, h=grp.h,
                       lvl=level, ind=2*level+2, pad=' '))
            shapes = shape.find('v:Shapes', namespaces=VNSMAP)
            try:
                for child in shapes:
                    g = self.process_visio_shape(child,
                                                 level=level+1, parent=grp)
                    if g is not None:
                        group.append(g)
            except TypeError:  # shapes is None
                vprint('TypeError due to shapes is None')
            bytes = []
            for s in group:
                if isinstance(s, Byte):
                    bytes.append(s)
                elif isinstance(s, Dot3):
                    # Revisit: only consider full-width Dot3 instances
                    grp = Array(shape, id, group, level=level, parent=parent,
                                dots=s)
                    vprint('{pad: <{ind}}Array: ID={id}@{x:.3f},{y:.3f}({w:.3f}x{h:.3f}), level={lvl}'.
                           format(
                               id=id, x=grp.x, y=grp.y, w=grp.w, h=grp.h,
                               lvl=level, ind=2*level+2, pad=' '))
            bits = []
            for s in group:
                if isinstance(s, Bit):
                    b = s.closest_byte(bytes)
                    if b is not None:
                        s.set_byte(b)
                    else:
                        print('{} has no closest Byte in {}'.format(s, grp))
                    bits.append(s)
            if len(bytes) > 0:
                return Header(shape, id, group, bits, bytes, level=level, parent=parent)
            grp.setup_instances()  # must be after child shapes processed
            return grp
        else:
            print('  ID={}, Type={} (unknown)'.format(id, type))
            return None

class Section():
    def __init__(self, word, para, style):
        self.word = word
        self.para = para
        self.style = style
        self.end = None
        self.refs = word.para_refs(para)
        self.name = get_text(para)
        self.tbls = []

    def __repr__(self):
        return '{obj}(style={style}, name={name}: refs={refs})'.format(
            style=self.style, name=self.name, refs=self.refs,
            obj=type(self).__name__)

    def set_end(self, end_sect):
        self.end = end_sect.para

    def process_section1(self):
        nxt = self.para.getnext()
        prev2 = None
        prev = self.para
        while nxt is not None and nxt != self.end:
            if nxt.tag == WNSC+'tbl':
                tbl = Table(self.word, self, nxt, prev, prev2)
                self.tbls.append(tbl)
            prev2 = prev
            prev = nxt
            nxt = nxt.getnext()
        tlen = len(self.tbls)
        if tlen > 0:
            vprint('process_section1: {}: tables={}'.format(self, self.tbls))
            for ref in self.refs:
                self.word.add_bookmark(ref, self,
                                       self.tbls[0] if tlen == 1 else None)

    def process_section2(self):
        tlen = len(self.tbls)
        if tlen > 0:
            vprint('process_section2: {}: tables={}'.format(self, self.tbls))
            for tbl in self.tbls:
                self.word.process_table(tbl)

    def fuzzy_table_match(self, name):
        return fuzzy_process.extractOne(name, self.tbls)

    def table_match(self, name):
        if len(self.tbls) == 0:
            return None
        elif len(self.tbls) == 1:
            return self.tbls[0]
        else:
            return self.fuzzy_table_match(name)[0]

class Table():
    def __init__(self, word, sect, tbl, title_para, fig_para):
        self.word = word
        self.sect = sect
        self.tbl = tbl
        self.title_para = title_para
        self.title = Para(para=title_para)
        if fig_para is not None:
            fig = Para(para=fig_para)
            m = word.re_fig.match(fig.text)
            if m:
                fig_refs = word.para_refs(fig_para)
                for ref in fig_refs:
                    word.add_bookmark(ref, sect, self)
        self.refs = word.para_refs(title_para)
        txt = self.title.text
        vprint('Table: title={}, refs={}'.format(txt, self.refs), min=2)
        for ref in self.refs:
            word.add_bookmark(ref, sect, self)
        m = word.re_tbl.match(txt)
        if m:
            self.chap = m.group('chap')
            self.num  = m.group('num')
            self.name = m.group('name')
        else:
            self.chap = '?'
            self.num = '?'
            self.name = '???'

    def __repr__(self):
        return '{obj}({chap}-{num}: "{name}")'.format(
            chap=self.chap, num=self.num, name=self.name,
            obj=type(self).__name__)

    def __str__(self):
        return '{obj} {chap}-{num}: {name}'.format(
            chap=self.chap, num=self.num, name=self.name,
            obj=type(self).__name__)

class Word():
    re_word_doc   = re.compile('word/document.xml')
    re_fig        = re.compile('^Figure.*[\s]'+
                               '(?P<chap>[\dA-Z]+)-'+
                               '(?P<num>[\d]+):[\s]+'+
                               '(?P<name>.*)$')
    re_tbl        = re.compile('^Table.*[\s]'+
                               '(?P<chap>[\dA-Z]+)-'+
                               '(?P<num>[\d]+):[\s]+'+
                               '(?P<name>.*)$')
    re_type_tbl   = re.compile('Table.*:  Control Space structure Type Encodings')
    re_class_tbl  = re.compile('Table.*:  Component Class Encodings')
    re_uuid_tbl   = re.compile('^Table.*:  (?P<kind>.*) UUID')
    re_fields_tbl = re.compile('^Table.*[\s]'+
                               '(?P<chap>[\dA-Z]+)-'+
                               '(?P<num>[\d]+):  '+
                               '(?P<name>.* (Structure|Table|Record|Header|Entry)) (Fields|Common Fields)$')
    re_desc_ref   = re.compile('^[\s]*See[\s]+REF[\s]'+
                               '(?P<ref>_Ref[\d]+).* MERGEFORMAT '+
                               '(?P<txt>[\w\s-]+)')
    re_desc_ref4  = re.compile('^.*See:'+
                               '[\s]*REF[\s](?P<ref1>_Ref[\d]+).*'+
                               '[\s]+REF[\s](?P<ref2>_Ref[\d]+).*'+
                               '[\s]+REF[\s](?P<ref3>_Ref[\d]+).*'+
                               '[\s]+REF[\s](?P<ref4>_Ref[\d]+)')
    re_ptr_ref    = re.compile('.*[Pp]oint(s|er)? to.*[\s]+REF[\s]'+
                               '(?P<ref>_Ref[\d]+).* MERGEFORMAT '+
                               '(?P<txt>.+)')
    re_subfields_tbl = re.compile('^Table.*[\s]'+
                                  '(?P<chap>[\dA-Z]+)-'+
                                  '(?P<num>[\d]+):[\s]+'+
                                  '(?P<name>.*)$')
    re_struct_name = re.compile('[()]')
    re_desc_name = re.compile('[—\.]')
    re_field_vals = re.compile('<name>((?P<val>([01]b|0x[\dA-F]+))|'+
                               '(?P<min>0x[\dA-F]+)-'+
                               '(?P<max>0x[\dA-F]+))[\s]?—'+
                               '(?P<name>[^;]+)'+
                               '(;[\s]*(?P<other>.*))?</name>')
    re_subfields = re.compile('<name>(Bit (?P<bit>([\d]+))|'+
                              'Bits (?P<max>[\d]+):'+
                              '(?P<min>[\d]+))[\s]?—'+
                              '(?P<name>[^;]+)'+
                              '(;[\s]*(?P<other>.*))?</name>')
    re_struct_vers = re.compile('<name>'+
                                '(?P<name>.*) Version '+
                                '(=|shall be) (?P<vers>([01]b|0x[\dA-F]+)).*'+
                                '</name>')
    re_reserved = re.compile('^(?P<rv>(Reserved|RsvdP|RsvdZ))')
    re_fields_sub = re.compile(' (Fields|Common Fields)$')

    def __init__(self, filename, all_structs):
        self.filename = filename
        self.all_structs = all_structs
        self.bookmarks = {}
        self.all_ptrs = {}
        self.sections = []
        self.uuids = []
        self.generic_struct = Structure(None, 'struct', None)
        self.generic_fname = FieldName(
            xml='<name>Control Structure PTR <ix>n</ix></name>')

        with zipfile.ZipFile(filename, 'r') as self.zip:
            zipinfo = self.zip.infolist()

            for inf in filter(self.match_word_doc, zipinfo):
                self.process_word_doc(inf)

    def struct_by_name(self, name):
        return self.all_structs.members[name]

    def struct_by_ptr(self, name):
        return self.all_ptrs[name]

    def match_struct_names(self, name):
        f = filter(lambda x: self.match_struct_name(x, name),
                   self.all_structs.members.items())
        return [x[1] for x in f]

    def match_struct_name(self, item, name):
        return name in item[0]

    def match_word_doc(self, zipinfo):
        return Word.re_word_doc.match(zipinfo.filename)

    def add_bookmark(self, ref, sect, table):
        self.bookmarks[ref] = (sect, table)

    def process_word_doc(self, zipinfo):
        vprint(zipinfo.filename)
        with self.zip.open(zipinfo) as f:
            self.tree = etree.parse(f)
            root = self.tree.getroot()
            vprint('root={}'.format(root.tag), min=2)
            body = root[0]
            vprint('body={}'.format(body.tag), min=2)
            for para in body.iterfind('w:p', namespaces=VNSMAP):
                self.process_word_para(para)
            prev = None
            for sect in self.sections:
                self.set_section_end(sect, prev)
                prev = sect
            for sect in self.sections:
                sect.process_section1()
            for sect in self.sections:
                sect.process_section2()
            for s in self.all_structs:
                s.link_PTRs(self)

    def para_style(self, para):
        style = None
        ppr = para.find('w:pPr', namespaces=VNSMAP)
        if ppr is not None:
            pstyle = ppr.find('w:pStyle', namespaces=VNSMAP)
            if pstyle is not None:
                style = pstyle.get(WNSC+'val')
        return style

    def para_refs(self, para):
        refs = []
        for b in para.iterfind('w:bookmarkStart', namespaces=VNSMAP):
            name = b.get(WNSC+'name')
            if name[0:4] == '_Ref':
                refs.append(name)
        return refs

    def process_word_para(self, para):
        style = self.para_style(para)
        if style is not None and style[0:7] == 'Heading':
            self.sections.append(Section(self, para, style))

    def set_section_end(self, sect, prev_sect):
        if prev_sect is not None:
            prev_sect.set_end(sect)

    def process_table(self, table):
        tp = table.title
        txt = tp.text
        vprint('tbl: title={}, tp={}'.format(txt, tp), min=2)
        mf = Word.re_fields_tbl.match(txt)
        mu = Word.re_uuid_tbl.match(txt)
        if mf:
            self.process_fields_table(table)
        elif Word.re_type_tbl.match(txt):
            self.process_type_table(table)
        elif Word.re_class_tbl.match(txt):
            self.process_class_table(table)
        elif mu:
            self.process_uuid_table(table, mu)

    def fields_bits(self, fields):
        field_names = {}
        field_count = 0
        total_bits = 0
        num_elems = fields[0].num_elems
        if num_elems is not None and num_elems > 0:
            return num_elems * fields[0].num_bits
        for f in fields:
            total_bits += 0 if f.num_bits < 0 else f.num_bits
            f_name = f.fname.text
            m = re_range_match.fullmatch(f_name)
            if m:  # strip off [xx:yy]
                f_name = m.group('name')
            if not m or not f_name in field_names:
                field_count += 1
                field_names[f_name] = True
        return total_bits // field_count

    def process_fields_table_row(self, table, s, row, fname):
        value = None
        tcs = row.findall('w:tc', namespaces=VNSMAP)
        deleted = row.get(WNSC+'rsidDel')
        if deleted is not None:
            vprint('skipping deleted row {}'.format(get_text(tcs[0])), min=1)
            return fname
        desc_tc = tcs[4]
        prev_name = fname
        fname = FieldName(para=tcs[0].find('w:p', namespaces=VNSMAP))
        if fname.text == 'Version (Vers)':
            fname.text = 'Vers'
            try:
                value = int(self.get_vers_desc(desc_tc), base=0)
            except TypeError:
                print('Invalid structure version "{}" in {}'.format(
                    get_text(desc_tc), table))
        elif fname.text == '':
            fname = prev_name
        try:
            fld_name = fname.text
        except AttributeError:
            vprint('tbl row: missing field name in {}'.format(fld_name), min=1)
            return fname
        size  = Para(tc=tcs[1]).text
        if size == '-' or size == '':
            bits = None
        else:
            try:
                bits = int(size)
            except ValueError:
                vprint('tbl: invalid Size, "{}"'.format(size))
                bits = None
        mo   = Para(tc=tcs[2]).text
        acc  = Para(tc=tcs[3]).text
        vals, subfields, desc = self.get_field_desc(desc_tc)
        paras = desc_tc.findall('w:p', namespaces=VNSMAP)
        first = paras[0]
        first_txt = get_text(first)
        first_para = Para(para=first, ref=True)
        access, mo = self.adjust_acc_mo(acc, mo, desc)
        try:
            fields = (s.field_by_name(fname),)  # one-element tuple
        except KeyError:
            try:
                fields = tuple(s.match_field_name(fname))
                vprint('{} matches {} fields: {}'.format(fname, len(fields),
                                                         fields), min=1)
            except AttributeError:
                fields = []
        if len(fields) == 0:
            print('No such field: from {}, in {}: "{}"'.format(
                table, s, fname))
            return fname
        ptr = re_ptr_match.fullmatch(fname.name)
        ptr_ref = None
        if ptr:
            pr = Word.re_ptr_ref.fullmatch(first_txt)
            if pr:
                try:
                    g = pr.group('ref')
                    ptr_ref = self.bookmarks[g]
                    vprint('PTR ref: {} has ref {}'.format(fname.name, g), min=1)
                except KeyError:
                    print('{}, field "{}" reference {} is not a field table'.format(
                        table, fld_name, g))
            else:
                vprint('no PTR ref: {}'.format(fname.name), min=1)
        for sub in subfields:
            for f in filter(sub.within, fields):
                f.add_subfield(sub)
        struct_bits = self.fields_bits(fields)
        for f in fields:
            if value is not None:
                f.value = value
            if (bits is not None and bits != struct_bits and f.num_bits > 0):
                print('Wrong field width: {}, field "{}", table {} != structure {}'.format(
                        table, fname, bits, struct_bits))
            f.mo = mo
            f.access = access
            if vals is not None and len(vals) > 0:
                f.vals = vals
            if ptr:
                f.ptr = PTR(f, fname, ptr_ref)
                s.PTRs.append(f.ptr)
        # end for f
        r = Word.re_desc_ref.fullmatch(first_txt)
        r4 = Word.re_desc_ref4.match(desc)
        if r:
            try:
                g = r.group('ref')
                if g != first_para._ref:
                    vprint('badref: Field "{}" has badref {}'.format(fld_name, g), min=2)
                    g = first_para._ref
                ref = self.bookmarks[g]
            except KeyError:
                print('{}, field "{}" reference {} is not a subfield table'.format(
                    table, fld_name, g))
                return fname
            vprint('ref: Field "{}" has ref {}'.format(fld_name, g), min=2)
            self.process_subfields_table(ref, fields, fld_name, g)
            return fname
        elif r4:
            try:
                g = (r4.group('ref1'),
                     r4.group('ref2'),
                     r4.group('ref3'),
                     r4.group('ref4'))
                refs = [self.bookmarks[x] for x in g]
            except KeyError:
                vprint('Field "{}" has unknown reference {}'.format(fld_name, g))
                return fname
            vprint('ref: Field "{}" has refs {}'.format(fld_name, g), min=2)
            for ref, f in zip(refs, fields):
                self.process_subfields_table(ref, (f,), fld_name, g)

    def process_fields_table(self, table):
        name = Word.re_fields_sub.sub('', table.name)
        vprint('tbl: {}'.format(table), min=1)
        is_table = True if name[-5:] == 'Table' else False
        is_struct = True if name[-9:] == 'Structure' else False
        tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
        hdr = next(tr, None)  # get the table header row
        if not self.check_fields_hdr(hdr):
            print('Invalid header: {}'.format(table))
            return
        try:
            structs = (self.struct_by_name(name),)  # one-element tuple
        except KeyError:
            structs = self.match_struct_names(name)

        if len(structs) == 0:
            vprint('tbl fields: {} not found'.format(name), min=1)
            return

        for s in structs:
            # Type & Size don't appear in Fields Tables, but they have known
            # properties (for Structures) or don't exist (for Tables)
            try:
                ty = s.field_by_name('Type')
                ty.mo = 'M'
                ty.access = 'RO'
            except KeyError:
                if is_struct:
                    print('Type is missing: {}'.format(table))
                    continue
            try:
                sz = s.field_by_name('Size')
                sz.mo = 'M'
                sz.access = 'RO'
            except KeyError:
                if is_struct:
                    print('Size is missing: {}'.format(table))
                    continue
            fname = None
            if len(structs) > 1 and s != structs[0]:
                # Reset tr/hdr iterator
                vprint('tbl structs: processing {} resetting tr/hdr'.format(s), min=1)
                tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
                hdr = next(tr, None)  # skip the table header row
            for row in tr:
                fname = self.process_fields_table_row(table, s, row, fname)
            # end for row
            try:
                s.set_size()
            except AttributeError:
                print('Error in set_size: {}'.format(table))
        # end for s

    def process_subfields_table(self, ref, fields, fld_name, g):
        sect, table = ref
        if table is None:
            table = sect.table_match(fld_name)
            vprint('tbl: "{}" fuzzy matched to {}'.format(
                fld_name, table), min=1)
        vprint('tbl: Subfield {}'.format(table), min=2)
        tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
        hdr = next(tr, None)  # get the table header row
        exp = self.check_subfields_hdr(hdr)
        if not exp:
            print('Invalid subfield header: {} from "{}" ({})'.format(
                table, fld_name, g))
            return
        for row in tr:
            tcs = row.findall('w:tc', namespaces=VNSMAP)
            loc = Para(tc=tcs[exp.index(('Bit Location',))])
            acc = Para(tc=tcs[exp.index(('Access',))]).text
            desc_tc = tcs[exp.index(('Description',))]
            sub_name, sub_vals, desc = self.get_subfield_desc(desc_tc)
            vprint('tbl: Subfield: loc={}, acc={}, name={}, vals={}, desc={}'.format(
                loc, acc, sub_name, sub_vals, desc), min=2)
            if loc.name == '<para></para>':
                print('{}, subfield {} has no Bit Location'.format(
                    table, desc))
                continue
            access = self.adjust_acc_mo(acc, None, desc)[0]
            sub = Subfield(loc, access, sub_name, sub_vals)
            for f in filter(sub.within, fields):
                f.add_subfield(sub)
        # end for row
        for f in fields:
            num_bits = f.num_bits
            subfield_bits = f.subfield_bits
            if num_bits != subfield_bits:
                print('Wrong subfield width: {}, field "{}" num_bits {} != subfield_bits {}'.format(
                    table, f.name, num_bits, subfield_bits))

    def check_fields_hdr(self, hdr):
        tcs = hdr.findall('w:tc', namespaces=VNSMAP)
        expected = [('Field Name',), ('Size (bits)',),
                    ('M / O','MO','M/O'),  ('Access',), ('Description',)]
        if len(tcs) != len(expected):
            vprint('header: Found {} columns, expected {}'.format(len(tcs), len(expected)))
            return False
        for tc, exp in zip(tcs, expected):
            txt = get_text(tc)
            if txt not in exp:
                vprint('header: Found {}, expected {}'.format(txt, exp), min=2)
                return False
        return True

    def check_subfields_hdr(self, hdr):
        tcs = hdr.findall('w:tc', namespaces=VNSMAP)
        expected = [[('Bit Location',),               ('Access',), ('Description',)],
                    [('Bit Location',), ('Default',), ('Access',), ('Description',)],
                    [('Bit Location',), ('Access',),
                     ('Packet Validation Error','Update C-Status',), ('Description',)],
                    [('Bit Location',), ('Access',), ('Error Severity',),
                     ('Packet Validation Error',), ('Description',)]
        ]
        lens = [len(e) for e in expected]
        if len(tcs) not in lens:
            vprint('subfield header: Found {} columns, expected {}'.format(len(tcs), lens))
            return False
        for ex, index in zip(expected, range(len(lens))):
            if len(tcs) != lens[index]:
                continue
            match = True
            for tc, exp in zip(tcs, ex):
                txt = get_text(tc)
                if txt not in exp:
                    match = False
            if match:
                return ex
        # end for ex
        return False

    def process_type_table(self, table):
        vprint('found Control Space structure Type Encodings')
        self.types = {}
        tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
        next(tr, None)  # skip the table header row

        for row in tr:
            tc = row.findall('w:tc', namespaces=VNSMAP)
            val = Para(tc=tc[0]).text
            txt = Para(tc=tc[1]).text
            parts = Word.re_struct_name.split(txt)
            if len(parts) <= 2:
                name = Word.re_struct_name.split(txt)[0].rstrip()
            elif len(parts) == 3:
                name = ' '.join((parts[0] + parts[2]).split())
            vprint('type {}: "{}"'.format(val, name))
            if name == 'Reserved':
                continue
            self.types[name] = int(val, base=0)
        for s in self.all_structs:
            try:
                if s.group.pointers:
                    if len(s.group.pointers) > 1:
                        ptrs = [p.ptr for p in s.group.pointers]
                    else:
                        ptrs = s.group.pointers[0].ptr.split(' | ')
                    s.set_ptr(ptrs)
                    for ptr in ptrs:
                        self.all_ptrs[ptr] = s
            except AttributeError:
                pass
            try:
                type = self.types[s.kind.fname.text]
                s.set_type(type)
                ty = s.field_by_name('Type')
                ty.value = type
                vers = s.field_by_name('Vers')
                s.set_vers(vers.value)
            except KeyError:
                pass

    def process_uuid_table(self, table, m):
        kind = m.group('kind')
        if kind[-5:] == ' Type':
            kind = kind[:-5]
        vprint('found {} UUIDs'.format(kind))
        tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
        next(tr, None)  # skip the table header row

        for row in tr:
            tc = row.findall('w:tc', namespaces=VNSMAP)
            name = get_all_text(tc[0])
            uuid_txt = get_text(tc[1])
            vprint('{}: "{}"'.format(name, uuid_txt))
            self.uuids.append(DefinedUuid(name, uuid.UUID(uuid_txt[2:]), kind))

    def process_class_table(self, table):
        vprint('found Component Class Encodings')
        self.classes = []
        tr = table.tbl.iterfind('w:tr', namespaces=VNSMAP)
        next(tr, None)  # skip the table header row

        for row in tr:
            tc = row.findall('w:tc', namespaces=VNSMAP)
            val = get_text(tc[0])
            name = get_all_text(tc[1])
            vprint('{}: "{}"'.format(val, name))
            if '-' in val:
                continue
            self.classes.append(ComponentClass(int(val, base=0), name))

    def adjust_acc_mo(self, acc, mo, desc):
        if acc == '-' or acc == '':
            m = Word.re_reserved.match(desc)
            if m:
                access = m.group('rv')
                if mo == '-':
                    mo = None
            else:
                access = None
        else:
            access = acc
        return access, mo

    def get_field_desc(self, desc_tc):
        paras = desc_tc.findall('w:p', namespaces=VNSMAP)
        first = paras[0]
        try:
            rest = paras[1:]
        except IndexError:
            rest = None
        vals = []
        subfields = []
        for para in rest:
            fname = FieldName(para=para)
            mv = Word.re_field_vals.fullmatch(fname.name)
            ms = Word.re_subfields.fullmatch(fname.name)
            if mv:
                vals.append(FieldVal(mv))
            elif ms:
                bit = ms.group('bit')
                max_bit = ms.group('max')
                min_bit = ms.group('min')
                if bit is not None:
                    sub_loc = Para(txt='{}'.format(bit))
                else:
                    sub_loc = Para(txt='{}:{}'.format(max_bit, min_bit))
                sub_fname = FieldName(name=ms.group('name'))
                subfields.append(Subfield(sub_loc, None, sub_fname, None))
        return (vals, subfields, get_text(desc_tc))

    def get_vers_desc(self, desc_tc):
        vers = None
        first = desc_tc.find('w:p', namespaces=VNSMAP)
        fname = FieldName(para=first)
        m = Word.re_struct_vers.fullmatch(fname.name)
        if m:
            vers = m.group('vers')
        return vers

    def get_subfield_desc(self, desc_tc):
        paras = desc_tc.findall('w:p', namespaces=VNSMAP)
        first = paras[0]
        try:
            rest = paras[1:]
        except IndexError:
            rest = None
        fname = FieldName(para=first, split=Word.re_desc_name.split)
        vals = []
        for para in rest:
            fname_rest = FieldName(para=para)
            m = Word.re_field_vals.fullmatch(fname_rest.name)
            if m:
                vals.append(FieldVal(m))
        return (fname, vals, Para(tc=desc_tc).text)

class GenZ():
    writable = [ 'RW', 'RWS', 'RW1C', 'RW1CS', 'WO' ]

    def __init__(self, name, ctl, pkt, word):
        self.tree = etree.Element(name)
        now = datetime.now()
        self.tree.set('generated', '{}'.format(now))
        self.tree.set('ctl', '{}'.format(ctl))
        self.tree.set('pkt', '{}'.format(pkt))
        self.tree.set('word', '{}'.format(word))
        self.etree = etree.ElementTree(self.tree)

    def get_field_prop(self, f, prop, default=None):
        fp = f.get(prop)
        if fp is None:
            val = default
        elif fp == 'UNKNOWN':
            val = UNKNOWN
        else:
            val = int(fp)
        return val

    def check_subfield(self, name, sf, off, subfield_names):
        nm = sf.find('name')
        min_bit = self.get_field_prop(sf, 'min_bit')
        max_bit = self.get_field_prop(sf, 'max_bit')
        num_bits = self.get_field_prop(sf, 'num_bits')
        sf_rw_ba = BitArray(num_bits)  # num_bits of 0's
        sf_rv_ba = BitArray(num_bits)  # num_bits of 0's
        sf_acc = sf.get('access')
        if sf_acc in GenZ.writable:
            sf_rw_ba = ~sf_rw_ba  # num_bits of 1's
        elif sf_acc == 'Reserved':
            sf_rv_ba = ~sf_rv_ba  # num_bits of 1's
        nm_str = etree.tostring(nm, encoding='unicode')
        if (nm_str in subfield_names and not
            (nm_str[0:10] == '<name>Rsvd' or nm_str[0:14] == '<name>Reserved')):
            minb, maxb = subfield_names[nm_str]
            print('Duplicate subfield: "{}" in {} at offset {}, bits {}:{}, {}:{}'.format(
                nm_str, name, off, max_bit, min_bit, maxb, minb))
        else:
            subfield_names[nm_str] = (min_bit, max_bit)
        return (sf_rw_ba, sf_rv_ba, min_bit)

    def check_field(self, name, f, off, field_names):
        min_bit = self.get_field_prop(f, 'min_bit')
        num_bits = self.get_field_prop(f, 'num_bits')
        base_bit = self.get_field_prop(f, 'base_bit', default=0)
        if num_bits > 0:
            f_rw_ba = BitArray(num_bits)  # num_bits of 0's
            f_rv_ba = BitArray(num_bits)  # num_bits of 0's
        else:
            f_rw_ba = None
            f_rv_ba = None
        nm = f.find('name')
        nm_str = etree.tostring(nm, encoding='unicode')
        if nm_str in field_names:
            print('Duplicate field: "{}" in {} at offsets {}, {}'.format(
                nm_str, name, field_names[nm_str], off))
        else:
            field_names[nm_str] = off
        # check for RW PTR fields
        f_acc = f.get('access')
        if f_acc in GenZ.writable and f_rw_ba is not None:
            f_rw_ba = ~f_rw_ba  # num_bits of 1's
        elif f_acc == 'Reserved' and f_rv_ba is not None:
            f_rv_ba = ~f_rv_ba  # num_bits of 1's
        if re_ptr_match.fullmatch(nm_str) is not None:
            if not (f_acc == 'RO' or f_acc == 'HwInit'):
                vprint('check found RW PTR: {}, access={}'.format(
                    nm_str, f_acc))
        subfield_names = {}
        sf_rw = False
        sf_rv = False
        for sf in f.iter('subfield'):
            sf_ret = self.check_subfield(name, sf, off, subfield_names)
            sf_rw_ba, sf_rv_ba, sf_min_bit = sf_ret
            f_rw_ba.overwrite(sf_rw_ba, sf_min_bit-base_bit)
            f_rv_ba.overwrite(sf_rv_ba, sf_min_bit-base_bit)
            if sf_rw_ba.any(1):
                sf_rw = True
            if sf_rv_ba.any(1):
                sf_rv = True
        if sf_rw and sf_rv:
            print('{}, offset {}: Mixed RW and Reserved subfields in {}'.format(
                name, off, nm_str))
        return (f_rw_ba, f_rv_ba, min_bit)

    def check_offset(self, name, o, prev_off, field_names):
        off = o.get('value')
        o_num_bits = int(o.get('num_bits'))
        o_rw_ba = BitArray(o_num_bits)
        o_rv_ba = BitArray(o_num_bits)
        if off is None:
            print('Offset has no value (prev_off={}) in {}'.format(
                prev_off, name))
        elif off == prev_off and off != 'UNKNOWN':
            print('Duplicate offset: {} in {}'.format(off, name))
        writable_fields = []
        for f in o:
            f_ret = self.check_field(name, f, off, field_names)
            f_rw_ba, f_rv_ba, f_min_bit = f_ret
            if f_rw_ba is not None and f_rw_ba.any(1):
                writable_fields.append((f, f_min_bit, len(f_rw_ba)))
            o_rw_ba.overwrite(f_rw_ba, f_min_bit)
            o_rv_ba.overwrite(f_rv_ba, f_min_bit)

        for f, f_min_bit, f_num_bits in writable_fields:
            adj_min, adj_num = field_power_of_2_aligned(f_min_bit, f_num_bits)
            adj_rw_ba = o_rw_ba[adj_min:adj_min+adj_num]
            adj_rv_ba = o_rv_ba[adj_min:adj_min+adj_num]
            if adj_rw_ba.any(1) and adj_rv_ba.any(1):
                nm = f.find('name')
                nm_str = etree.tostring(nm, encoding='unicode')
                print('{}, offset {}: Mixed RW and Reserved fields near {}'.format(
                    name, off, nm_str))
        return off

    def check_element(self, name, e):
        prev_off = None
        field_names = {}
        for o in e:
            if o.tag == 'offset':
                prev_off = self.check_offset(name, o, prev_off, field_names)
            elif o.tag == 'array':
                prev_off = self.check_array(name, o, prev_off)
            else:
                print('Unknown element {} in array element {}'.format(o.tag, e))
        # end for o

    def check_array(self, name, a, prev_off):
        off = a.get('offset')
        if off is None:
            print('Array has no offset (prev_off={}) in {}'.format(
                prev_off, name))
        elif off == prev_off and off != 'UNKNOWN':
            print('Duplicate offset: {} in {}'.format(off, name))
        for e in a:
            self.check_element(name, e)
        return off

    def check(self, word):
        st = self.tree.find('structs')
        ty_cnt = 0
        ptr_cnt = 0
        for s in st:
            name = s.get('name')
            ty = s.get('type')
            if ty is not None:
                ty_cnt += 1
            ptr = s.get('ptr')
            if ptr is not None:
                ptr_cnt += 1
            prev_off = None
            field_names = {}
            for o in s:
                if o.tag == 'offset':
                    prev_off = self.check_offset(name, o, prev_off, field_names)
                elif o.tag == 'array':
                    prev_off = self.check_array(name, o, prev_off)
                else:
                    print('Unknown element {} in struct {}'.format(o.tag, s))
            # end for o
        # end for s
        pk = self.tree.find('packets')
        cl = self.tree.find('classes')
        uu = self.tree.find('uuids')
        print('Extracted {} structs ({} have a type [{} expected], {} have a ptr, {} are unknown), {} packets, {} classes, {} uuids'.format(
            len(st), ty_cnt, len(word.types), ptr_cnt,
            len(st) - ty_cnt - ptr_cnt,
            len(pk), len(cl), len(uu)))

# Utitlity functions
def vprint(str, min=0):
    if args.verbose > min:
        print(str)

def round_down_n(x, n):
    return (x & -n)

def round_up_n(x, n):
    return ((x + (n - 1)) & -n)

def clz(n):  # count leading zeros
    return (67 - len(bin(-n)) & ~n >> 64)

def clp2(n):  # ceiling least power of 2
    return 0 if n <= 0 else (1 << (64 - clz(n - 1)))

def flp2(n):  # floor least power of 2
    return 0 if n <=0 else (1 << (63 - clz(n)))

def field_power_of_2_aligned(f_min_bit, f_num_bits):
    # first, byte align min/num
    adj_min = round_down_n(f_min_bit, 8)
    bits_added = f_min_bit - adj_min
    adj_num = round_up_n(f_num_bits + bits_added, 8)
    # next, convert to bytes and round up to next power of 2
    num_bytes = (adj_num) // 8
    adj_bits = clp2(num_bytes) * 8
    adj_min = round_down_n(adj_min, adj_bits)
    return (adj_min, adj_bits)

def single_space(str):
    return ' '.join(str.split())

def get_text(obj):
    return obj.xpath('string()').rstrip()

def get_all_text(obj):
    return ' '.join([get_text(t) for t in obj.findall('.//w:t', namespaces=VNSMAP)])

def get_para_text(para, tree, split=None, ref=False):
    field_txt = ''
    ref_txt = None
    e = tree
    last_e = e
    tail = False
    next_tail = False
    finished = False
    first = True
    runs = []
    for elem in para:
        if elem.tag == WNSC+'r':
            runs.append(elem)
        elif elem.tag == WNSC+'ins':
            runs.extend(elem.findall('w:r', namespaces=VNSMAP))
    # end for elem
    for r in runs:
        rPr = r.find('w:rPr', namespaces=VNSMAP)
        if rPr is not None:
            vertAlign = rPr.find('w:vertAlign', namespaces=VNSMAP)
            if vertAlign is not None:
                val = vertAlign.get(WNSC+'val')
                if val == 'superscript':
                    tail = False
                    next_tail = True
                    e = etree.SubElement(tree, 'sup')
                elif val == 'subscript':
                    tail = False
                    next_tail = True
                    e = etree.SubElement(tree, 'sub')
        # end if rPr
        hyphen = r.find('w:noBreakHyphen', namespaces=VNSMAP)
        if hyphen is not None:
            txt = '-'
            if tail:
                e.tail = txt if e.tail is None else e.tail + txt
                last_e = e
            else:
                e.text = txt if e.text is None else e.text + txt
                last_e = e
            field_txt += txt
        t = r.find('w:t', namespaces=VNSMAP)
        if t is not None:
            preserve = (t.get(XMLNSC+'space') is not None or
                        t.text[-1] == '\xa0')  # non-breaking space
            txt = (t.text.replace('\xa0', ' ') if preserve else
                   single_space(t.text.strip()))
            if first:
                first = False
                txt = txt.lstrip()
            if split is not None:
                parts = split(txt, 2)
                if len(parts) > 1:
                    txt = parts[0].rstrip()
                    finished = True
            wild = find(txt, '*')
            if len(wild) > 0:  # * UEP Mask
                consumed = 0
                for w in wild:
                    w = w - consumed
                    if tail:
                        e.tail = (txt[:w] if e.tail is None else
                                  e.tail + txt[:w])
                    else:
                        e.text = (txt[:w] if e.text is None else
                                  e.text + txt[:w])
                    e = etree.SubElement(tree, 'wild')
                    txt = txt[w+1:]
                    tail = True
                    consumed += w+1
                # end for w
            elif txt[-10:] == ' n Control':  # Component CAP n Control
                e.text = txt[:-9]
                e = etree.SubElement(tree, 'ix')
                e.text = 'n'
                txt = ' Control'
                tail = True
            elif txt[-2:] == ' n':
                if tail:
                    e.tail = txt[:-1] if e.tail is None else e.tail + txt[:-1]
                else:
                    e.text = txt[:-1] if e.text is None else e.text + txt[:-1]
                e = etree.SubElement(tree, 'ix')
                txt = 'n'
                tail = False
            if tail:
                e.tail = txt if e.tail is None else e.tail + txt
                last_e = e
            else:
                e.text = txt if e.text is None else e.text + txt
                last_e = e
            field_txt += txt
        # end if t
        if ref:
            it = r.find('w:instrText', namespaces=VNSMAP)
            if it is not None:
                r2 = re_desc_ref2.fullmatch(it.text)
                if r2:
                    ref_txt = r2.group('ref')
            # end if it
        # end if ref
        if next_tail:
            tail = True
        if finished:
            break
    # end for r
    if last_e is not None:
        if last_e.tail is not None and len(last_e.tail):
            last_e.tail = last_e.tail.rstrip()
        elif last_e.text is not None and len(last_e.text):
            last_e.text = last_e.text.rstrip()
    return (field_txt.strip(), ref_txt)

def packet_sort(pkt):
    return pkt.name

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('ctl', help='Visio file defining the control structs')
    parser.add_argument('pkt', help='Visio file defining the packet formats')
    parser.add_argument('word', help='Word file containing the specification')
    parser.add_argument('-x', '--xmlfile', help='output XML file')
    parser.add_argument('-p', '--pretty', help='output pretty XML version of Word and Visio files')
    parser.add_argument('-v', '--verbose', help='increase verbose level',
                        action='count', default=0)
    parser.add_argument('-i', '--ids', help='include IDs in XML output',
                        action='store_true')
    parser.add_argument('-k', '--keyboard', help='invoke interactive keyboard',
                        action='store_true')
    parser.add_argument('-P', '--post_mortem', action='store_true',
                        help='enter debugger on uncaught exception')
    global args
    args = parser.parse_args()
    out = open(args.xmlfile, 'wb') if args.xmlfile else sys.stdout
    pretty_w = open('word-'+args.pretty, 'w') if args.pretty else None
    pretty_v = open('visio-'+args.pretty, 'w') if args.pretty else None
    genz = GenZ('genz', args.ctl, args.pkt, args.word)

    vprint('Processing structs from {}'.format(args.ctl))
    all_structs = Visio(args.ctl, 'table')
    structs = etree.SubElement(genz.tree, 'structs')

    vprint('Processing packets from {}'.format(args.pkt))
    all_packets = Visio(args.pkt, 'packet')
    packets = etree.SubElement(genz.tree, 'packets')
    for s in sorted(all_packets, key=packet_sort):
        s.create_xml(packets)

    if pretty_v is not None:
        for tree in all_structs.trees:
            print(etree.tostring(tree, pretty_print=True, encoding=str),
                  end='', file=pretty_v)
        for tree in all_packets.trees:
            print(etree.tostring(tree, pretty_print=True, encoding=str),
                  end='', file=pretty_v)

    vprint('Processing tables from {}'.format(args.word))
    word = Word(args.word, all_structs)

    if pretty_w is not None:
        print(etree.tostring(word.tree, pretty_print=True, encoding=str),
              end='', file=pretty_w)

    for s in sorted(all_structs, key=Structure.sort_key):
        s.create_xml(structs)

    classes = etree.SubElement(genz.tree, 'classes')
    for c in word.classes:
        c.create_xml(classes)

    uuids = etree.SubElement(genz.tree, 'uuids')
    for uu in word.uuids:
        uu.create_xml(uuids)

    genz.etree.write(file=out, encoding='utf-8', pretty_print=True,
                     xml_declaration=True)

    genz.check(word)

    if args.keyboard:
        keyboard()

if __name__ == '__main__':
    try:
        main()
    except Exception as post_err:
        if args.post_mortem:
            traceback.print_exc()
            post_mortem()
        else:
            raise

/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude
-/
import TDCSGCompute.Field

/-!
# Compact storage of orbit points

`PointSet` stores the points of an orbit in insertion order in one flat `ByteArray`: each point is
`d` coefficients in two's complement, little-endian, `width` bytes each (`width ∈ {1, 2, 4, 8}`).
A separate open-addressing hash table (linear probing, load factor at most `2/3`) holds 32-bit
indices into that array, so a point costs `d * width` bytes of data plus 6 to 12 bytes of table.

Insertion order doubles as the breadth-first frontier: the points of generation `g + 1` are exactly
those inserted while generation `g` is being expanded, so no separate queue is needed.

Overflow is never silent. Before a point is stored, every coefficient is range-checked against the
current width; if one does not fit, the whole array is re-encoded at the next width (and the table
rebuilt), up to 8 bytes. A coefficient outside the signed 64-bit range is a fatal error, reported
to the caller.
-/

namespace TDCSGCompute

/-- Whether `c` fits in `width` bytes in two's complement, i.e. `-2 ^ k ≤ c < 2 ^ k` with
`k = 8 * width - 1`: the arithmetic shift `c >>> k` is then `0` or `-1`. -/
@[inline] def fitsWidth (width : Nat) (c : Int) : Bool :=
  let s := c >>> (8 * width - 1)
  s == 0 || s == -1

/-- The smallest width in `{1, 2, 4, 8}` at least `w0` that holds every coefficient of `z`, or
`none` if a coefficient needs more than 8 bytes. -/
def widthFor (w0 : Nat) (z : Elem) : Option Nat :=
  [1, 2, 4, 8].find? (fun w ↦ w ≥ w0 && z.all (fitsWidth w))

/-- Append the coefficients of `z` to `buf` at width `width` (which must hold them). -/
@[inline] def encodePoint (width : Nat) (buf : ByteArray) (z : Elem) : ByteArray := Id.run do
  let mut b := buf
  for c in z do
    let u := (Int64.ofInt c).toUInt64
    for j in [0:width] do
      b := b.push (u >>> (8 * j).toUInt64).toUInt8
  return b

/-- The `i`-th coefficient stored at byte offset `off`, sign-extended to 64 bits. -/
@[inline] def readCoeff (width : Nat) (data : ByteArray) (off i : Nat) : Int64 :=
  let b := off + i * width
  let g (j : Nat) : UInt64 := (data.get! (b + j)).toUInt64
  match width with
  | 1 => (g 0).toUInt8.toInt8.toInt64
  | 2 => (g 0 ||| (g 1 <<< 8)).toUInt16.toInt16.toInt64
  | 4 => (g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24)).toUInt32.toInt32.toInt64
  | _ => (g 0 ||| (g 1 <<< 8) ||| (g 2 <<< 16) ||| (g 3 <<< 24) ||| (g 4 <<< 32) |||
      (g 5 <<< 40) ||| (g 6 <<< 48) ||| (g 7 <<< 56)).toInt64


/-- Decode the point stored at byte offset `off` (`d` coefficients of `width` bytes). -/
@[inline] def decodePoint (width d : Nat) (data : ByteArray) (off : Nat) : Elem := Id.run do
  let mut r : Elem := Array.emptyWithCapacity d
  for i in [0:d] do
    r := r.push (readCoeff width data off i).toInt
  return r

/-- The FNV-1a offset basis. -/
def fnvOffset : UInt64 := 0xcbf29ce484222325

/-- The FNV-1a prime. -/
def fnvPrime : UInt64 := 0x100000001b3

/-- First MurmurHash3 finalizer constant. -/
def murmur1 : UInt64 := 0xff51afd7ed558ccd

/-- Second MurmurHash3 finalizer constant. -/
def murmur2 : UInt64 := 0xc4ceb9fe1a85ec53

/-- FNV-1a over `len` bytes of `data` from `off`, followed by the 64-bit MurmurHash3 finalizer. -/
@[inline] def hashBytes (data : ByteArray) (off len : Nat) : UInt64 := Id.run do
  let mut h : UInt64 := fnvOffset
  for i in [0:len] do
    h := (h ^^^ (data.get! (off + i)).toUInt64) * fnvPrime
  h := h ^^^ (h >>> 33)
  h := h * murmur1
  h := h ^^^ (h >>> 33)
  h := h * murmur2
  h := h ^^^ (h >>> 33)
  return h

/-- Whether `len` bytes of `a` from `offA` equal `len` bytes of `b` from `offB`. -/
@[inline] def bytesEq (a : ByteArray) (offA : Nat) (b : ByteArray) (offB len : Nat) : Bool :=
  Id.run do
    for i in [0:len] do
      if a.get! (offA + i) != b.get! (offB + i) then return false
    return true

/-- A zero-filled `ByteArray` of size `2 ^ k`, built by repeated doubling. -/
def zeroBytesPow2 (k : Nat) : ByteArray := Id.run do
  let mut b : ByteArray := ByteArray.empty.push 0
  for _ in [0:k] do
    b := b ++ b
  return b

/-- Read the little-endian 32-bit slot `i`. -/
@[inline] def readSlot (slots : ByteArray) (i : Nat) : Nat :=
  let o := 4 * i
  ((slots.get! o).toUInt32 ||| ((slots.get! (o + 1)).toUInt32 <<< 8) |||
    ((slots.get! (o + 2)).toUInt32 <<< 16) ||| ((slots.get! (o + 3)).toUInt32 <<< 24)).toNat

/-- Write the little-endian 32-bit slot `i`. -/
@[inline] def writeSlot (slots : ByteArray) (i v : Nat) : ByteArray :=
  let o := 4 * i
  let w := v.toUInt32
  let s := slots.set! o w.toUInt8
  let s := s.set! (o + 1) (w >>> 8).toUInt8
  let s := s.set! (o + 2) (w >>> 16).toUInt8
  s.set! (o + 3) (w >>> 24).toUInt8

/-- The largest number of points a `PointSet` can hold (32-bit indices, `0` meaning empty). -/
def maxPoints : Nat := 2 ^ 32 - 2

/-- A set of points of `ℤ[ζ_n]` stored compactly, in insertion order. -/
structure PointSet where
  /-- Number of coefficients per point. -/
  deg : Nat
  /-- Bytes per coefficient. -/
  width : Nat
  /-- The points, `deg * width` bytes each. -/
  data : ByteArray
  /-- Number of points. -/
  size : Nat
  /-- Open-addressing table of `index + 1` (0 = empty), 4 bytes per slot. -/
  slots : ByteArray
  /-- `log₂` of the number of slots. -/
  logCap : Nat
  /-- The number of slots minus one. -/
  mask : Nat
  /-- Number of times the coefficients were re-encoded at a larger width. -/
  widenings : Nat

namespace PointSet

/-- An empty set for points with `deg` coefficients, starting at `width` bytes per coefficient. -/
def empty (deg width : Nat) (logCap : Nat := 10) : PointSet :=
  { deg, width, data := ByteArray.empty, size := 0, slots := zeroBytesPow2 (logCap + 2),
    logCap, mask := 2 ^ logCap - 1, widenings := 0 }

/-- Bytes per point. -/
@[inline] def stride (s : PointSet) : Nat := s.deg * s.width

/-- The `i`-th point. -/
@[inline] def get (s : PointSet) (i : Nat) : Elem := decodePoint s.width s.deg s.data (i * s.stride)


/-- Mix one 64-bit word into a hash state. -/
@[inline] def mixWord (h w : UInt64) : UInt64 := (h ^^^ w) * fnvPrime

/-- Final avalanche step (the 64-bit MurmurHash3 finalizer). -/
@[inline] def finalizeHash (h : UInt64) : UInt64 :=
  let h := h ^^^ (h >>> 33)
  let h := h * murmur1
  let h := h ^^^ (h >>> 33)
  let h := h * murmur2
  h ^^^ (h >>> 33)

/-- Hash of a point from its coefficients (independent of the storage width). -/
@[inline] def hashElem (z : Elem) : UInt64 :=
  finalizeHash (z.foldl (fun h c ↦ mixWord h (Int64.ofInt c).toUInt64) fnvOffset)

/-- Hash of the point stored at byte offset `off`; equal to `hashElem` of the decoded point. -/
@[inline] def hashStored (width d : Nat) (data : ByteArray) (off : Nat) : UInt64 := Id.run do
  let mut h := fnvOffset
  for i in [0:d] do
    h := mixWord h (readCoeff width data off i).toUInt64
  return finalizeHash h

/-- Whether the point stored at byte offset `off` equals `z` (whose coefficients fit). -/
@[inline] def storedEq (width : Nat) (data : ByteArray) (off : Nat) (z : Elem) : Bool := Id.run do
  for i in [0:z.size] do
    if readCoeff width data off i != Int64.ofInt z[i]! then return false
  return true

/-- Rebuild the table with `2 ^ logCap` slots from the data array. -/
def rebuild (s : PointSet) (logCap : Nat) : PointSet := Id.run do
  let mask := 2 ^ logCap - 1
  let mut slots := zeroBytesPow2 (logCap + 2)
  let st := s.stride
  for i in [0:s.size] do
    let mut pos := (hashStored s.width s.deg s.data (i * st)).toNat &&& mask
    while readSlot slots pos != 0 do
      pos := (pos + 1) &&& mask
    slots := writeSlot slots pos (i + 1)
  return { s with slots, logCap, mask }

/-- Re-encode all points at a larger width and rebuild the table. -/
def widen (s : PointSet) (width : Nat) : PointSet := Id.run do
  let mut data := ByteArray.emptyWithCapacity (s.size * s.deg * width)
  for i in [0:s.size] do
    data := encodePoint width data (s.get i)
  let s' := { s with width, data, widenings := s.widenings + 1 }
  return s'.rebuild s.logCap

/-- Result of an insertion. -/
inductive InsertResult where
  /-- The point was already present. -/
  | present (s : PointSet)
  /-- The point was added. -/
  | added (s : PointSet)
  /-- A coefficient does not fit in 8 bytes, or the set is full. -/
  | overflow (s : PointSet)

/-- Find the slot of `z` (whose coefficients fit the width): `(slot, index + 1 or 0)`. -/
@[inline] def probe (s : PointSet) (z : Elem) : Nat × Nat := Id.run do
  let st := s.stride
  let mut pos := (hashElem z).toNat &&& s.mask
  while true do
    let v := readSlot s.slots pos
    if v == 0 then return (pos, 0)
    if storedEq s.width s.data ((v - 1) * st) z then return (pos, v)
    pos := (pos + 1) &&& s.mask
  return (pos, 0)

/-- Whether `z` is in the set (a `z` that does not fit the current width is not). -/
def contains (s : PointSet) (z : Elem) : Bool :=
  if !z.all (fitsWidth s.width) then false else (s.probe z).2 != 0

/-- Insert `z`, widening the encoding or growing the table as needed. -/
def insert (s : PointSet) (z : Elem) : InsertResult := Id.run do
  let mut s := s
  if !z.all (fitsWidth s.width) then
    match widthFor s.width z with
    | none => return .overflow s
    | some w => s := s.widen w
  let (pos, v) := s.probe z
  if v != 0 then return .present s
  if s.size ≥ maxPoints then return .overflow s
  let idx := s.size
  let ⟨deg, width, data, size, slots, logCap, mask, widenings⟩ := s
  let data := encodePoint width data z
  let slots := writeSlot slots pos (idx + 1)
  let t : PointSet := { deg, width, data, size := size + 1, slots, logCap, mask, widenings }
  -- keep the load factor at most 2/3
  if 3 * t.size > 2 * (t.mask + 1) then
    return .added (t.rebuild (t.logCap + 1))
  return .added t

/-- Approximate memory in bytes held by the data array and the table. -/
def memoryBytes (s : PointSet) : Nat := s.data.size + s.slots.size

end PointSet

end TDCSGCompute

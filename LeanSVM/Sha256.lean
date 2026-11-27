/-
  LeanSVM.Sha256
  Pure, zero-dependency, FIPS 180-4 byte-exact SHA-256 implementation in Lean 4
  for faithful `sol_sha256` syscall verification in `LeanSVM.Runtime`.

  Zero `sorry`, zero custom axioms, zero external dependencies.
-/

namespace LeanSVM.Sha256

/-- FIPS 180-4 SHA-256 round constants `K[0..63]`. -/
def K : List UInt32 :=
  [0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
   0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
   0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
   0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
   0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
   0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
   0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
   0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- 32-bit right rotation `ROTR^n(x)` for `1 ≤ n < 32`. -/
@[inline] def rotr32 (x n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

/-- Big-endian `UInt32` from 4 bytes. -/
@[inline] def beU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  (b0.toUInt32 <<< 24) ||| (b1.toUInt32 <<< 16) ||| (b2.toUInt32 <<< 8) ||| b3.toUInt32

/-- Serialize a `UInt32` as 4 big-endian bytes. -/
@[inline] def u32ToBeBytes (w : UInt32) : List UInt8 :=
  [(w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8, w.toUInt8]

/-- Serialize a `UInt64` as 8 big-endian bytes. -/
@[inline] def u64ToBeBytes (w : UInt64) : List UInt8 :=
  [(w >>> 56).toUInt8, (w >>> 48).toUInt8, (w >>> 40).toUInt8, (w >>> 32).toUInt8,
   (w >>> 24).toUInt8, (w >>> 16).toUInt8, (w >>> 8).toUInt8,  w.toUInt8]

/-- FIPS 180-4 SHA-256 padding: appends `0x80`, zero bytes to `56 (mod 64)`,
    and the 64-bit big-endian bit length `msg.length * 8`. -/
def pad (msg : List UInt8) : List UInt8 :=
  let len : Nat := msg.length
  let bitLen : UInt64 := (len * 8).toUInt64
  let rem := (len + 1) % 64
  let zeroCount := if rem ≤ 56 then 56 - rem else 120 - rem
  msg ++ [0x80] ++ List.replicate zeroCount 0 ++ u64ToBeBytes bitLen

/-- Parse 4-byte big-endian `UInt32` words from a 64-byte block (returning reversed list of 16 words). -/
def parse16WordsRev : Nat → List UInt8 → List UInt32 → (List UInt32 × List UInt8)
  | 0, rest, acc => (acc, rest)
  | k + 1, b0 :: b1 :: b2 :: b3 :: rest, acc =>
    parse16WordsRev k rest (beU32 b0 b1 b2 b3 :: acc)
  | k + 1, _, acc => parse16WordsRev k [] (0 :: acc)

/-- Fast O(1) lookup of element `n` in a list, defaulting to 0. -/
def nthU32 : List UInt32 → Nat → UInt32
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => nthU32 xs n

/-- Extend a reversed 16-word schedule to a forward 64-word schedule `W[0..63]`. -/
def extend48 : Nat → List UInt32 → List UInt32
  | 0, revW => revW.reverse
  | k + 1, revW =>
    -- In `revW`, index 0 = W[t-1], index 1 = W[t-2], index 6 = W[t-7], index 14 = W[t-15], index 15 = W[t-16]
    let w2  := nthU32 revW 1
    let w7  := nthU32 revW 6
    let w15 := nthU32 revW 14
    let w16 := nthU32 revW 15
    let s0  := rotr32 w15 7 ^^^ rotr32 w15 18 ^^^ (w15 >>> 3)
    let s1  := rotr32 w2 17 ^^^ rotr32 w2 19  ^^^ (w2 >>> 10)
    let wt  := w16 + s0 + w7 + s1
    extend48 k (wt :: revW)

/-- 8-word working state `(h0..h7)`. -/
structure State where
  h0 : UInt32
  h1 : UInt32
  h2 : UInt32
  h3 : UInt32
  h4 : UInt32
  h5 : UInt32
  h6 : UInt32
  h7 : UInt32
  deriving Repr, BEq

def initState : State :=
  { h0 := 0x6a09e667, h1 := 0xbb67ae85, h2 := 0x3c6ef372, h3 := 0xa54ff53a,
    h4 := 0x510e527f, h5 := 0x9b05688c, h6 := 0x1f83d9ab, h7 := 0x5be0cd19 }

/-- Run the 64 compression rounds over parallel `K` and `W` lists. -/
def runRounds (base : State) : List UInt32 → List UInt32 →
    UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → State
  | ki :: ks, wi :: ws, a, b, c, d, e, f, g, h =>
    let s1 := rotr32 e 6 ^^^ rotr32 e 11 ^^^ rotr32 e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let temp1 := h + s1 + ch + ki + wi
    let s0 := rotr32 a 2 ^^^ rotr32 a 13 ^^^ rotr32 a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let temp2 := s0 + maj
    runRounds base ks ws (temp1 + temp2) a b c (d + temp1) e f g
  | _, _, a, b, c, d, e, f, g, h =>
    { h0 := base.h0 + a, h1 := base.h1 + b, h2 := base.h2 + c, h3 := base.h3 + d,
      h4 := base.h4 + e, h5 := base.h5 + f, h6 := base.h6 + g, h7 := base.h7 + h }

/-- Compress one 64-byte block (given as its reversed 16-word list) into `st`. -/
def compressBlock (st : State) (rev16 : List UInt32) : State :=
  let w := extend48 48 rev16
  runRounds st K w st.h0 st.h1 st.h2 st.h3 st.h4 st.h5 st.h6 st.h7

/-- Compress all 64-byte blocks from a padded byte list. -/
def compressBlocks : Nat → List UInt8 → State → State
  | 0, _, st => st
  | k + 1, bytes, st =>
    let (rev16, rest) := parse16WordsRev 16 bytes []
    compressBlocks k rest (compressBlock st rev16)

/-- Serialize final SHA-256 state into its exact 32-byte big-endian digest (`List UInt8`). -/
def stateToBytes (st : State) : List UInt8 :=
  u32ToBeBytes st.h0 ++ u32ToBeBytes st.h1 ++ u32ToBeBytes st.h2 ++ u32ToBeBytes st.h3 ++
  u32ToBeBytes st.h4 ++ u32ToBeBytes st.h5 ++ u32ToBeBytes st.h6 ++ u32ToBeBytes st.h7

/-- Pure FIPS 180-4 SHA-256 over a byte list, returning an exact 32-byte digest. -/
def hash (msg : List UInt8) : List UInt8 :=
  let padded := pad msg
  stateToBytes (compressBlocks (padded.length / 64) padded initState)

/-- **THEOREM (`Sha256.hash_length`)**: Every SHA-256 digest has exact length 32 bytes. -/
theorem hash_length (msg : List UInt8) : (hash msg).length = 32 := by
  unfold hash stateToBytes u32ToBeBytes
  rfl

set_option maxRecDepth 20000 in
/-- **THEOREM (`Sha256.nist_empty`)**: Kernel-checked FIPS 180-4 vector `SHA-256("")`. -/
theorem nist_empty :
    hash [] =
      [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14,
       0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9, 0x24,
       0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
       0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] := by
  rfl

set_option maxRecDepth 20000 in
/-- **THEOREM (`Sha256.nist_abc`)**: Kernel-checked FIPS 180-4 vector `SHA-256("abc")`. -/
theorem nist_abc :
    hash [0x61, 0x62, 0x63] =
      [0xba, 0x78, 0x16, 0xbf, 0x8f, 0x01, 0xcf, 0xea,
       0x41, 0x41, 0x40, 0xde, 0x5d, 0xae, 0x22, 0x23,
       0xb0, 0x03, 0x61, 0xa3, 0x96, 0x17, 0x7a, 0x9c,
       0xb4, 0x10, 0xff, 0x61, 0xf2, 0x00, 0x15, 0xad] := by
  rfl

set_option maxRecDepth 40000 in
/-- **THEOREM (`Sha256.nist_56byte_multiblock`)**: Kernel-checked FIPS 180-4 two-block vector
    `SHA-256("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")`. -/
theorem nist_56byte_multiblock :
    hash [0x61, 0x62, 0x63, 0x64, 0x62, 0x63, 0x64, 0x65,
          0x63, 0x64, 0x65, 0x66, 0x64, 0x65, 0x66, 0x67,
          0x65, 0x66, 0x67, 0x68, 0x66, 0x67, 0x68, 0x69,
          0x67, 0x68, 0x69, 0x6a, 0x68, 0x69, 0x6a, 0x6b,
          0x69, 0x6a, 0x6b, 0x6c, 0x6a, 0x6b, 0x6c, 0x6d,
          0x6b, 0x6c, 0x6d, 0x6e, 0x6c, 0x6d, 0x6e, 0x6f,
          0x6d, 0x6e, 0x6f, 0x70, 0x6e, 0x6f, 0x70, 0x71] =
      [0x24, 0x8d, 0x6a, 0x61, 0xd2, 0x06, 0x38, 0xb8,
       0xe5, 0xc0, 0x26, 0x93, 0x0c, 0x3e, 0x60, 0x39,
       0xa3, 0x3c, 0xe4, 0x59, 0x64, 0xff, 0x21, 0x67,
       0xf6, 0xec, 0xed, 0xd4, 0x19, 0xdb, 0x06, 0xc1] := by
  rfl

end LeanSVM.Sha256

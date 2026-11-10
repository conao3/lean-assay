import Plausible

/-!
Generators that `#assay` puts in place of plausible's defaults.

plausible's `Char` generator draws code points below the sample size, so it never produces a
character outside the Basic Multilingual Plane. Specifications about UTF-8 and UTF-16 widths need
characters of every width, so this generator mixes ASCII with two-, three- and four-byte
characters.
-/

open Plausible

namespace Assay

/-- Characters of every UTF-8 width and of both UTF-16 widths, with the code points at each boundary
between widths. -/
def wideChars : List Char :=
  " aZ09\n\r\t".toList ++ ['é', 'ß', 'Ω', 'あ', '漢', '€', '😀', '𝔸', '𠀋'] ++
    [Char.ofNat 0x7F, Char.ofNat 0x80, Char.ofNat 0x7FF, Char.ofNat 0x800, Char.ofNat 0xFFFF,
      Char.ofNat 0x10000, Char.ofNat 0x10FFFF]

instance (priority := high) charArbitrary : Arbitrary Char where
  arbitrary := do
    let i ← Gen.choose Nat 0 (wideChars.length - 1) (by decide)
    return wideChars[i.val]!

end Assay

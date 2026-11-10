import Assay
import Examples.LspTouchstone.Position

/--
info: theorems, run on the original functions:
  T1 unitWidth_pos: 1000/1000 random inputs satisfy the hypotheses
  T2 resolve_offset: 569/1000 random inputs satisfy the hypotheses
  T3 resolve_beyond: 332/1000 random inputs satisfy the hypotheses
  T4 resolve_splits.1: 62/5000 random inputs satisfy the hypotheses
  T5 resolve_splits.2: 62/5000 random inputs satisfy the hypotheses
  T6 resolve_splits.3: 62/5000 random inputs satisfy the hypotheses

mutant                                                                                    T1  T2  T3  T4  T5  T6   verdict
unitWidth := fun _ _ => default                                                           ✗   ✗   ·   ?   ?   ?    killed
unitWidth := fun _ _ => zero                                                              ✗   ✗   ·   ?   ?   ?    killed
unitWidth: 9:17: | .utf8, c => c.utf8Size ↦ if c.val < 0x10000 then 1 else 2              ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 9:17: | .utf8, c => c.utf8Size ↦ 1                                             ·   ·   ·   ?   ?   ?    untested
unitWidth: 10:18: | .utf16, c => if c.val < 0x10000 then 1 else 2 ↦ c.utf8Size            ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:18: | .utf16, c => if c.val < 0x10000 then 1 else 2 ↦ 1                     ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:42: swap the branches of if                                                 ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:27: swap the operands of <                                                  ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:27: < ↦ ≤                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:27: < ↦ >                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:29: 0x10000 ↦ 65537                                                         ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:29: 0x10000 ↦ 65535                                                         ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:42: 1 ↦ 2                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:42: 1 ↦ 0                                                                   ✗   ✗   ·   ·   ·   ·    killed
unitWidth: 10:49: 2 ↦ 3                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 10:49: 2 ↦ 1                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 11:18: 1 ↦ 2                                                                   ·   ·   ·   ·   ·   ·    HOLE
unitWidth: 11:18: 1 ↦ 0                                                                   ✗   ✗   ·   ·   ·   ·    killed
shift := fun x => x                                                                       -   ✗   ✗   ·   ·   ✗    killed
shift: 19:17: | .exact n => .exact (n + 1) ↦ .clamped (n + 1)                             -   ✗   ·   ·   ·   ·    killed
shift: 19:17: | .exact n => .exact (n + 1) ↦ .splitsChar (n + 1)                          -   ✗   ·   ✗   ✗   ✗    killed
shift: 20:19: | .clamped n => .clamped (n + 1) ↦ .exact (n + 1)                           -   ·   ✗   ·   ·   ·    killed
shift: 20:19: | .clamped n => .clamped (n + 1) ↦ .splitsChar (n + 1)                      -   ·   ✗   ✗   ·   ✗    killed
shift: 21:22: | .splitsChar n => .splitsChar (n + 1) ↦ .exact (n + 1)                     -   ·   ·   ·   ·   ·    HOLE
shift: 21:22: | .splitsChar n => .splitsChar (n + 1) ↦ .clamped (n + 1)                   -   ·   ·   ·   ·   ·    HOLE
shift: 19:27: + ↦ -                                                                       -   ✗   ·   ·   ·   ·    killed
shift: 19:29: 1 ↦ 2                                                                       -   ✗   ·   ·   ·   ·    killed
shift: 19:29: 1 ↦ 0                                                                       -   ✗   ·   ·   ·   ·    killed
shift: 20:31: + ↦ -                                                                       -   ·   ✗   ·   ·   ·    killed
shift: 20:33: 1 ↦ 2                                                                       -   ·   ✗   ·   ·   ·    killed
shift: 20:33: 1 ↦ 0                                                                       -   ·   ✗   ·   ·   ·    killed
shift: 21:37: + ↦ -                                                                       -   ·   ·   ·   ·   ✗    killed
shift: 21:39: 1 ↦ 2                                                                       -   ·   ·   ✗   ✗   ·    killed
shift: 21:39: 1 ↦ 0                                                                       -   ·   ·   ·   ·   ✗    killed
resolveList: 24:14: | [], 0 => .exact 0 ↦ .clamped 0                                      -   ✗   ·   ·   ·   ·    killed
resolveList: 25:18: | [], _ + 1 => .clamped 0 ↦ .exact 0                                  -   ·   ✗   ·   ·   ·    killed
resolveList: 27:5: | c :: cs, n => if n = 0 then .exact 0 else if n < unit… ↦ .exact 0    -   ✗   ✗   ?   ?   ?    killed
resolveList: 27:5: | c :: cs, n => if n = 0 then .exact 0 else if n < unit… ↦ .clamped 0  -   ✗   ✗   ?   ?   ?    killed
resolveList: 24:21: 0 ↦ 1                                                                 -   ✗   ·   ·   ·   ·    killed
resolveList: 25:27: 0 ↦ 1                                                                 -   ·   ✗   ·   ·   ·    killed
resolveList: 27:19: swap the branches of if                                               -   ✗   ✗   ·   ✗   ·    killed
resolveList: 27:10: = ↦ ≠                                                                 -   ✗   ✗   ·   ✗   ·    killed
resolveList: 27:12: 0 ↦ 1                                                                 -   ✗   ·   ·   ✗   ·    killed
resolveList: 27:26: 0 ↦ 1                                                                 -   ✗   ·   ·   ·   ·    killed
resolveList: 28:36: swap the branches of if                                               -   ✗   ✗   ·   ·   ✗    killed
resolveList: 28:15: swap the operands of <                                                -   ✗   ✗   ·   ·   ✗    killed
resolveList: 28:15: < ↦ ≤                                                                 -   ✗   ·   ·   ·   ✗    killed
resolveList: 28:15: < ↦ >                                                                 -   ✗   ✗   ·   ·   ✗    killed
resolveList: 28:48: 0 ↦ 1                                                                 -   ·   ·   ✗   ✗   ·    killed
resolveList: 29:31: swap the operands of -                                                -   ✗   ✗   ·   ·   ·    killed
resolveList: 29:31: - ↦ +                                                                 -   ✗   ·   ·   ·   ·    killed
offsetList := fun _ _ _ => default                                                        -   ✗   ✗   -   ·   ✗    killed
offsetList := fun _ _ _ => zero                                                           -   ✗   ✗   -   ·   ✗    killed
offsetList := fun _ _ x => x                                                              -   ✗   ✗   -   ·   ✗    killed
offsetList: 34:23: | c :: cs, i + 1 => unitWidth e c + offsetList e cs i ↦ 0              -   ✗   ✗   -   ·   ✗    killed
offsetList: 32:14: 0 ↦ 1                                                                  -   ✗   ·   -   ·   ·    killed
offsetList: 33:18: 0 ↦ 1                                                                  -   ✗   ·   -   ✗   ·    killed
offsetList: 34:18: 1 ↦ 0                                                                  -   ✗   ·   -   ✗   ·    killed
offsetList: 34:37: + ↦ -                                                                  -   ✗   ✗   -   ·   ✗    killed

72 mutants: 43 killed, 15 holes, 1 untested, 1 equivalent, 0 timed out, 12 stillborn
---
warning: hole: `unitWidth: 9:17: | .utf8, c => c.utf8Size ↦ if c.val < 0x10000 then 1 else 2` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf8, c := '漢'
---
warning: hole: `unitWidth: 10:18: | .utf16, c => if c.val < 0x10000 then 1 else 2 ↦ c.utf8Size` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '߿'
---
warning: hole: `unitWidth: 10:18: | .utf16, c => if c.val < 0x10000 then 1 else 2 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '😀'
---
warning: hole: `unitWidth: 10:42: swap the branches of if` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '߿'
---
warning: hole: `unitWidth: 10:27: swap the operands of <` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '߿'
---
warning: hole: `unitWidth: 10:27: < ↦ ≤` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '𐀀'
---
warning: hole: `unitWidth: 10:27: < ↦ >` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '߿'
---
warning: hole: `unitWidth: 10:29: 0x10000 ↦ 65537` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '𐀀'
---
warning: hole: `unitWidth: 10:29: 0x10000 ↦ 65535` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '￿'
---
warning: hole: `unitWidth: 10:42: 1 ↦ 2` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '߿'
---
warning: hole: `unitWidth: 10:49: 2 ↦ 3` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '😀'
---
warning: hole: `unitWidth: 10:49: 2 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf16, c := '😀'
---
warning: hole: `unitWidth: 11:18: 1 ↦ 2` satisfies every theorem but changes the output on an input that satisfies the hypotheses of unitWidth_pos: e := proved.Encoding.utf32, c := '\n'
---
warning: hole: `shift: 21:22: | .splitsChar n => .splitsChar (n + 1) ↦ .exact (n + 1)` satisfies every theorem but changes the output on an input that satisfies the hypotheses of resolve_splits.1: e := proved.Encoding.utf16, cs := ['あ', '𠀋', '€', 'ß'], n := 2, i := 1
---
warning: hole: `shift: 21:22: | .splitsChar n => .splitsChar (n + 1) ↦ .clamped (n + 1)` satisfies every theorem but changes the output on an input that satisfies the hypotheses of resolve_splits.1: e := proved.Encoding.utf16, cs := ['あ', '𠀋', '€', 'ß'], n := 2, i := 1
-/
#guard_msgs in
#assay proved.unitWidth proved.Resolution.shift proved.resolveList proved.offsetList

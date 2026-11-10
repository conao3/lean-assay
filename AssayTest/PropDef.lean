import Assay
import Examples.Forms.PropDef

/--
info: theorems, run on the original functions:
  T1 clampInRange_proven: 1000/1000 random inputs satisfy the hypotheses

mutant                                  T1   verdict
clampU8 := fun _ => default             ·    HOLE
clampU8 := fun _ => zero                ·    HOLE
clampU8: 4:17: swap the branches of if  ·    HOLE
clampU8: 4:8: swap the operands of <    ·    HOLE
clampU8: 4:8: < ↦ >                     ·    HOLE
clampU8: 4:17: 0 ↦ 1                    ·    HOLE
clampU8: 4:40: swap the branches of if  ·    HOLE
clampU8: 4:29: > ↦ <                    ·    HOLE

15 mutants: 0 killed, 8 holes, 0 untested, 7 equivalent, 0 timed out, 0 stillborn
---
warning: hole: `clampU8 := fun _ => default` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 1
---
warning: hole: `clampU8 := fun _ => zero` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 1
---
warning: hole: `clampU8: 4:17: swap the branches of if` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 1
---
warning: hole: `clampU8: 4:8: swap the operands of <` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 1
---
warning: hole: `clampU8: 4:8: < ↦ >` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 1
---
warning: hole: `clampU8: 4:17: 0 ↦ 1` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := -1
---
warning: hole: `clampU8: 4:40: swap the branches of if` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 0
---
warning: hole: `clampU8: 4:29: > ↦ <` satisfies every theorem but changes the output on an input that satisfies the hypotheses of clampInRange_proven: n := 0
-/
#guard_msgs in
#assay Forms.clampU8

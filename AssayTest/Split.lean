import Assay
import Examples.Forms.Split.Props

/--
info: theorems, run on the original functions:
  T1 addTwiceBounded_proven: 1000/1000 random inputs satisfy the hypotheses

mutant                              T1   verdict
cap := fun _ => default             ·    HOLE
cap := fun _ => zero                ·    HOLE
cap := fun x => x                   ✗    killed
cap: 4:18: swap the branches of if  ✗    killed
cap: 4:8: swap the operands of <    ✗    killed
cap: 4:8: < ↦ >                     ✗    killed
cap: 4:10: 10 ↦ 9                   ·    HOLE
cap: 4:25: 10 ↦ 11                  ✗    killed
cap: 4:25: 10 ↦ 9                   ·    HOLE

11 mutants: 5 killed, 4 holes, 0 untested, 2 equivalent, 0 timed out, 0 stillborn
---
warning: hole: `cap := fun _ => default` satisfies every theorem but changes the output on an input that satisfies the hypotheses of addTwiceBounded_proven: a := 1, b := 1
---
warning: hole: `cap := fun _ => zero` satisfies every theorem but changes the output on an input that satisfies the hypotheses of addTwiceBounded_proven: a := 1, b := 1
---
warning: hole: `cap: 4:10: 10 ↦ 9` satisfies every theorem but changes the output on an input that satisfies the hypotheses of addTwiceBounded_proven: a := 3, b := 3
---
warning: hole: `cap: 4:25: 10 ↦ 9` satisfies every theorem but changes the output on an input that satisfies the hypotheses of addTwiceBounded_proven: a := 4, b := 3
-/
#guard_msgs in
#assay Forms.Split.cap using Forms.Split.addTwiceBounded_proven

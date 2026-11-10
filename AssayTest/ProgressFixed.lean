import Assay
import Examples.LspTouchstoneFixed.Progress

/--
info: theorems, run on the original functions:
  T1 ended_accepts_nothing: 3/3 all inputs satisfy the hypotheses
  T2 only_begin_leaves_created.1: 1/9 all inputs satisfy the hypotheses
  T3 only_begin_leaves_created.2: 1/9 all inputs satisfy the hypotheses
  T4 only_report_or_end_leave_begun: 2/9 all inputs satisfy the hypotheses
  T5 begun_never_returns_to_created: 3/3 all inputs satisfy the hypotheses
  T6 nothing_after_end: 1000/1000 random inputs satisfy the hypotheses
  T7 accepted_runs_begin_first: 73/2857 random inputs satisfy the hypotheses
  T8 begin_reports_end: 1000/1000 random inputs satisfy the hypotheses

mutant                                                        T1  T2  T3  T4  T5  T6  T7  T8   verdict
step := fun _ _ => default                                    ·   ?   ?   ?   ·   ·   ?   ✗    killed
step := fun _ _ => none                                       ·   ?   ?   ?   ·   ·   ?   ✗    killed
step := fun _ _ => some created                               ✗   ✗   ✗   ✗   ✗   ✗   ✗   ✗    killed
step := fun _ _ => some begun                                 ✗   ✗   ·   ✗   ·   ✗   ✗   ✗    killed
step := fun _ _ => some ended                                 ✗   ✗   ✗   ✗   ·   ✗   ✗   ·    killed
step: 16:25: | .created, .begin => some .begun ↦ some .ended  ·   ·   ✗   ·   ·   ·   ·   ✗    killed
step: 16:25: | .created, .begin => some .begun ↦ none         ·   ?   ?   ·   ·   ·   ?   ✗    killed
step: 17:24: | .begun, .report => some .begun ↦ some .ended   ·   ·   ·   ✗   ·   ·   ·   ✗    killed
step: 17:24: | .begun, .report => some .begun ↦ none          ·   ·   ·   ·   ·   ·   ·   ✗    killed
step: 18:24: | .begun, .finish => some .ended ↦ some .begun   ·   ·   ·   ✗   ·   ·   ·   ✗    killed
step: 18:24: | .begun, .finish => some .ended ↦ none          ·   ·   ·   ·   ·   ·   ·   ✗    killed
step: 19:13: | _, _ => none ↦ some .begun                     ✗   ✗   ·   ✗   ·   ✗   ✗   ·    killed
step: 19:13: | _, _ => none ↦ some .ended                     ✗   ✗   ✗   ✗   ·   ✗   ✗   ·    killed
step: 19:3: add | .created, .report => some .begun            ·   ✗   ·   ·   ·   ·   ✗   ·    killed
step: 19:3: add | .created, .report => some .ended            ·   ✗   ✗   ·   ·   ·   ✗   ·    killed
step: 19:3: add | .created, .finish => some .begun            ·   ✗   ·   ·   ·   ·   ✗   ·    killed
step: 19:3: add | .created, .finish => some .ended            ·   ✗   ✗   ·   ·   ·   ✗   ·    killed
step: 19:3: add | .begun, .begin => some .begun               ·   ·   ·   ✗   ·   ·   ·   ·    killed
step: 19:3: add | .begun, .begin => some .ended               ·   ·   ·   ✗   ·   ·   ·   ·    killed

19 mutants: 19 killed, 0 holes, 0 untested, 0 equivalent, 0 stillborn
-/
#guard_msgs in
#assay proved.step

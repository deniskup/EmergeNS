(declare-const ent0 Bool)
(declare-const ent1 Bool)
(declare-const ent2 Bool)
(declare-const ent3 Bool)
(declare-const ent4 Bool)
(declare-const ent5 Bool)
(declare-const ent6 Bool)
(declare-const ent7 Bool)
(declare-const ent8 Bool)
(declare-const ent9 Bool)
(declare-const ent10 Bool)
(declare-const ent11 Bool)
(declare-const ent12 Bool)
(declare-const ent13 Bool)
(declare-const reac0 Bool)
(declare-const dir0 Bool)
(declare-const coef0 Int)
(declare-const reac1 Bool)
(declare-const dir1 Bool)
(declare-const coef1 Int)
(declare-const reac2 Bool)
(declare-const dir2 Bool)
(declare-const coef2 Int)
(declare-const reac3 Bool)
(declare-const dir3 Bool)
(declare-const coef3 Int)
(declare-const reac4 Bool)
(declare-const dir4 Bool)
(declare-const coef4 Int)
(declare-const reac5 Bool)
(declare-const dir5 Bool)
(declare-const coef5 Int)
(declare-const reac6 Bool)
(declare-const dir6 Bool)
(declare-const coef6 Int)
(declare-const reac7 Bool)
(declare-const dir7 Bool)
(declare-const coef7 Int)
(declare-const reac8 Bool)
(declare-const dir8 Bool)
(declare-const coef8 Int)
(declare-const reac9 Bool)
(declare-const dir9 Bool)
(declare-const coef9 Int)
(declare-const reac10 Bool)
(declare-const dir10 Bool)
(declare-const coef10 Int)
(assert (= dir0 (< coef0 0)))
(assert (= dir1 (< coef1 0)))
(assert (= dir2 (< coef2 0)))
(assert (= dir3 (< coef3 0)))
(assert (= dir4 (< coef4 0)))
(assert (= dir5 (< coef5 0)))
(assert (= dir6 (< coef6 0)))
(assert (= dir7 (< coef7 0)))
(assert (= dir8 (< coef8 0)))
(assert (= dir9 (< coef9 0)))
(assert (= dir10 (< coef10 0)))
(assert (=> reac0 (and(or ent1 ent0)(or ent2))))
(assert (=> reac1 (and(or ent1 ent1)(or ent3))))
(assert (=> reac2 (and(or ent1 ent4)(or ent5))))
(assert (=> reac3 (and(or ent1 ent2)(or ent7))))
(assert (=> reac4 (and(or ent0 ent6)(or ent10))))
(assert (=> reac5 (and(or ent3 ent2)(or ent10))))
(assert (=> reac6 (and(or ent1 ent8)(or ent11))))
(assert (=> reac7 (and(or ent0 ent8)(or ent12))))
(assert (=> reac8 (and(or ent2 ent2)(or ent13))))
(assert (=> reac9 (and(or ent1 ent5)(or ent13))))
(assert (=> reac10 (and(or ent0 ent7)(or ent13))))
(assert (=> ent0 (> (+ (ite reac0 (* -1 coef0) 0) (ite reac4 (* -1 coef4) 0) (ite reac7 (* -1 coef7) 0) (ite reac10 (* -1 coef10) 0) 0) 0)))
(assert (=> ent1 (> (+ (ite reac0 (* -1 coef0) 0) (ite reac1 (* -2 coef1) 0) (ite reac2 (* -1 coef2) 0) (ite reac3 (* -1 coef3) 0) (ite reac6 (* -1 coef6) 0) (ite reac9 (* -1 coef9) 0) 0) 0)))
(assert (=> ent2 (> (+ (ite reac0 (* 1 coef0) 0) (ite reac3 (* -1 coef3) 0) (ite reac5 (* -1 coef5) 0) (ite reac8 (* -2 coef8) 0) 0) 0)))
(assert (=> ent3 (> (+ (ite reac1 (* 1 coef1) 0) (ite reac5 (* -1 coef5) 0) 0) 0)))
(assert (=> ent4 (> (+ (ite reac2 (* -1 coef2) 0) 0) 0)))
(assert (=> ent5 (> (+ (ite reac2 (* 1 coef2) 0) (ite reac9 (* -1 coef9) 0) 0) 0)))
(assert (=> ent6 (> (+ (ite reac4 (* -1 coef4) 0) 0) 0)))
(assert (=> ent7 (> (+ (ite reac3 (* 1 coef3) 0) (ite reac10 (* -1 coef10) 0) 0) 0)))
(assert (=> ent8 (> (+ (ite reac6 (* -1 coef6) 0) (ite reac7 (* -1 coef7) 0) 0) 0)))
(assert (=> ent9 (> (+ 0) 0)))
(assert (=> ent10 (> (+ (ite reac4 (* 1 coef4) 0) (ite reac5 (* 1 coef5) 0) 0) 0)))
(assert (=> ent11 (> (+ (ite reac6 (* 1 coef6) 0) 0) 0)))
(assert (=> ent12 (> (+ (ite reac7 (* 1 coef7) 0) 0) 0)))
(assert (=> ent13 (> (+ (ite reac8 (* 1 coef8) 0) (ite reac9 (* 1 coef9) 0) (ite reac10 (* 1 coef10) 0) 0) 0)))
(assert ((_ at-most 11) ent0 ent1 ent2 ent3 ent4 ent5 ent6 ent7 ent8 ent9 ent10 ent11 ent12 ent13))
(assert ((_ at-least 11) ent0 ent1 ent2 ent3 ent4 ent5 ent6 ent7 ent8 ent9 ent10 ent11 ent12 ent13))
(assert ((_ at-least 11) reac0 reac1 reac2 reac3 reac4 reac5 reac6 reac7 reac8 reac9 reac10))
(assert ((_ at-most 11) reac0 reac1 reac2 reac3 reac4 reac5 reac6 reac7 reac8 reac9 reac10))
(assert (not (and reac3 (not dir3) reac8 dir8 reac10 (not dir10) ent2 ent7 ent13)))
(assert (not (and reac0 dir0 reac8 dir8 reac10 (not dir10) ent0 ent2 ent13)))
(assert (not (and reac0 dir0 reac8 dir8 reac9 (not dir9) ent1 ent2 ent13)))
(assert (not (and reac4 dir4 reac5 (not dir5) reac8 dir8 reac10 (not dir10) ent0 ent2 ent10 ent13)))
(assert (not (and reac0 dir0 reac3 dir3 reac9 (not dir9) reac10 dir10 ent1 ent2 ent7 ent13)))
(assert (not (and reac3 dir3 reac8 (not dir8) reac9 (not dir9) reac10 dir10 ent1 ent2 ent7 ent13)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac9 dir9 reac10 (not dir10) ent1 ent5 ent7 ent13)))
(assert (not (and reac0 dir0 reac4 (not dir4) reac5 dir5 reac9 (not dir9) reac10 dir10 ent0 ent1 ent2 ent10 ent13)))
(assert (not (and reac1 dir1 reac4 (not dir4) reac5 dir5 reac9 (not dir9) reac10 dir10 ent0 ent1 ent3 ent10 ent13)))
(check-sat)
(get-model)

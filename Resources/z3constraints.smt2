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
(declare-const reac11 Bool)
(declare-const dir11 Bool)
(declare-const coef11 Int)
(declare-const reac12 Bool)
(declare-const dir12 Bool)
(declare-const coef12 Int)
(declare-const reac13 Bool)
(declare-const dir13 Bool)
(declare-const coef13 Int)
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
(assert (= dir11 (< coef11 0)))
(assert (= dir12 (< coef12 0)))
(assert (= dir13 (< coef13 0)))
(assert (=> reac0 (and(or ent0 ent0) ent2)))
(assert (=> reac1 (and(or ent1 ent0) ent3)))
(assert (=> reac2 (and(or ent1 ent3) ent6)))
(assert (=> reac3 (and(or ent0 ent4) ent6)))
(assert (=> reac4 (and(or ent3 ent3) ent9)))
(assert (=> reac5 (and(or ent1 ent8) ent9)))
(assert (=> reac6 (and(or ent4 ent2) ent9)))
(assert (=> reac7 (and(or ent0 ent6) ent9)))
(assert (=> reac8 (and(or ent1 ent6) ent10)))
(assert (=> reac9 (and(or ent0 ent5) ent10)))
(assert (=> reac10 (and(or ent4 ent3) ent10)))
(assert (=> reac11 (and(or ent0 ent8) ent12)))
(assert (=> reac12 (and(or ent1 ent7) ent12)))
(assert (=> reac13 (and(or ent2 ent2) ent13)))
(assert (=> (and reac1 (not dir1)) (or (not ent1) (not ent0))))
(assert (=> (and reac2 (not dir2)) (or (not ent1) (not ent3))))
(assert (=> (and reac3 (not dir3)) (or (not ent0) (not ent4))))
(assert (=> (and reac5 (not dir5)) (or (not ent1) (not ent8))))
(assert (=> (and reac6 (not dir6)) (or (not ent4) (not ent2))))
(assert (=> (and reac7 (not dir7)) (or (not ent0) (not ent6))))
(assert (=> (and reac8 (not dir8)) (or (not ent1) (not ent6))))
(assert (=> (and reac9 (not dir9)) (or (not ent0) (not ent5))))
(assert (=> (and reac10 (not dir10)) (or (not ent4) (not ent3))))
(assert (=> (and reac11 (not dir11)) (or (not ent0) (not ent8))))
(assert (=> (and reac12 (not dir12)) (or (not ent1) (not ent7))))
(assert (=> ent0 (> (+ (ite reac0 (+ (- coef0) (- coef0)) 0)
 (ite reac1(- coef1) 0)
 (ite reac3(- coef3) 0)
 (ite reac7(- coef7) 0)
 (ite reac9(- coef9) 0)
 (ite reac11(- coef11) 0)
 0) 0)))
(assert (=> ent1 (> (+ (ite reac1(- coef1) 0)
 (ite reac2(- coef2) 0)
 (ite reac5(- coef5) 0)
 (ite reac8(- coef8) 0)
 (ite reac12(- coef12) 0)
 0) 0)))
(assert (=> ent2 (> (+ (ite reac0 coef0 0)
 (ite reac6(- coef6) 0)
 (ite reac13 (+ (- coef13) (- coef13)) 0)
 0) 0)))
(assert (=> ent3 (> (+ (ite reac1 coef1 0)
 (ite reac2(- coef2) 0)
 (ite reac4 (+ (- coef4) (- coef4)) 0)
 (ite reac10(- coef10) 0)
 0) 0)))
(assert (=> ent4 (> (+ (ite reac3(- coef3) 0)
 (ite reac6(- coef6) 0)
 (ite reac10(- coef10) 0)
 0) 0)))
(assert (=> ent5 (> (+ (ite reac9(- coef9) 0)
 0) 0)))
(assert (=> ent6 (> (+ (ite reac2 coef2 0)
 (ite reac3 coef3 0)
 (ite reac7(- coef7) 0)
 (ite reac8(- coef8) 0)
 0) 0)))
(assert (=> ent7 (> (+ (ite reac12(- coef12) 0)
 0) 0)))
(assert (=> ent8 (> (+ (ite reac5(- coef5) 0)
 (ite reac11(- coef11) 0)
 0) 0)))
(assert (=> ent9 (> (+ (ite reac4 coef4 0)
 (ite reac5 coef5 0)
 (ite reac6 coef6 0)
 (ite reac7 coef7 0)
 0) 0)))
(assert (=> ent10 (> (+ (ite reac8 coef8 0)
 (ite reac9 coef9 0)
 (ite reac10 coef10 0)
 0) 0)))
(assert (=> ent11 (> (+ 0) 0)))
(assert (=> ent12 (> (+ (ite reac11 coef11 0)
 (ite reac12 coef12 0)
 0) 0)))
(assert (=> ent13 (> (+ (ite reac13 coef13 0)
 0) 0)))
(assert (= (+ (ite ent0 1 0) (ite ent1 1 0) (ite ent2 1 0) (ite ent3 1 0) (ite ent4 1 0) (ite ent5 1 0) (ite ent6 1 0) (ite ent7 1 0) (ite ent8 1 0) (ite ent9 1 0) (ite ent10 1 0) (ite ent11 1 0) (ite ent12 1 0) (ite ent13 1 0)) 13))
(assert (= (+ (ite reac0 1 0) (ite reac1 1 0) (ite reac2 1 0) (ite reac3 1 0) (ite reac4 1 0) (ite reac5 1 0) (ite reac6 1 0) (ite reac7 1 0) (ite reac8 1 0) (ite reac9 1 0) (ite reac10 1 0) (ite reac11 1 0) (ite reac12 1 0) (ite reac13 1 0)) 13))
(assert (not (and reac2 (not dir2) reac4 dir4 reac7 (not dir7) ent3 ent6 ent9)))
(assert (not (and reac1 dir1 reac4 dir4 reac7 (not dir7) ent0 ent3 ent9)))
(assert (not (and reac0 dir0 reac6 dir6 reac7 (not dir7) ent0 ent2 ent9)))
(assert (not (and reac1 dir1 reac4 dir4 reac5 (not dir5) ent1 ent3 ent9)))
(assert (not (and reac4 dir4 reac7 (not dir7) reac9 dir9 reac10 (not dir10) ent0 ent3 ent9 ent10)))
(assert (not (and reac4 dir4 reac7 (not dir7) reac8 dir8 reac10 (not dir10) ent3 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac8 dir8 reac9 (not dir9) reac10 (not dir10) ent0 ent4 ent6 ent10)))
(assert (not (and reac2 (not dir2) reac3 (not dir3) reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent10)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac4 dir4 reac6 (not dir6) ent3 ent4 ent6 ent9)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent10)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac5 (not dir5) reac7 dir7 ent0 ent1 ent6 ent9)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac8 dir8 reac9 (not dir9) ent0 ent1 ent6 ent10)))
(assert (not (and reac1 (not dir1) reac2 dir2 reac8 dir8 reac10 (not dir10) ent1 ent3 ent6 ent10)))
(assert (not (and reac4 dir4 reac5 (not dir5) reac8 dir8 reac10 (not dir10) ent1 ent3 ent9 ent10)))
(assert (not (and reac2 dir2 reac4 (not dir4) reac5 (not dir5) reac7 dir7 ent1 ent3 ent6 ent9)))
(assert (not (and reac1 dir1 reac2 dir2 reac5 (not dir5) reac7 dir7 ent1 ent3 ent6 ent9)))
(assert (not (and reac1 dir1 reac8 (not dir8) reac9 (not dir9) reac10 dir10 ent0 ent1 ent3 ent10)))
(assert (not (and reac2 (not dir2) reac5 dir5 reac7 (not dir7) reac11 (not dir11) reac12 dir12 ent1 ent6 ent8 ent9 ent12)))
(assert (not (and reac2 (not dir2) reac6 (not dir6) reac7 dir7 reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 (not dir2) reac4 dir4 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 (not dir3) reac4 (not dir4) reac6 dir6 reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac6 (not dir6) reac7 dir7 reac9 (not dir9) reac10 dir10 ent0 ent4 ent6 ent9 ent10)))
(assert (not (and reac6 (not dir6) reac7 dir7 reac8 (not dir8) reac9 (not dir9) reac10 dir10 ent0 ent4 ent6 ent9 ent10)))
(assert (not (and reac1 dir1 reac5 (not dir5) reac7 dir7 reac9 (not dir9) reac10 dir10 ent0 ent1 ent3 ent9 ent10)))
(assert (not (and reac1 dir1 reac6 (not dir6) reac7 dir7 reac9 (not dir9) reac10 dir10 ent0 ent3 ent4 ent9 ent10)))
(assert (not (and reac4 (not dir4) reac6 (not dir6) reac7 dir7 reac9 (not dir9) reac10 dir10 ent0 ent3 ent4 ent9 ent10)))
(assert (not (and reac4 (not dir4) reac6 (not dir6) reac7 dir7 reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 (not dir3) reac4 (not dir4) reac7 dir7 reac8 (not dir8) reac10 dir10 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac6 (not dir6) reac7 dir7 reac8 dir8 reac9 (not dir9) ent0 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac5 (not dir5) reac7 dir7 reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac8 dir8 reac9 (not dir9) reac11 dir11 reac12 (not dir12) ent0 ent1 ent6 ent10 ent12)))
(assert (not (and reac1 dir1 reac9 (not dir9) reac10 dir10 reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent10 ent12)))
(assert (not (and reac2 dir2 reac8 dir8 reac9 (not dir9) reac11 dir11 reac12 (not dir12) ent0 ent1 ent6 ent10 ent12)))
(assert (not (and reac3 dir3 reac5 (not dir5) reac6 dir6 reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 dir2 reac5 (not dir5) reac6 dir6 reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac5 (not dir5) reac6 dir6 reac7 (not dir7) reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 (not dir2) reac6 dir6 reac7 (not dir7) reac8 dir8 reac10 (not dir10) ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 dir2 reac5 (not dir5) reac7 dir7 reac8 dir8 reac10 (not dir10) ent1 ent3 ent6 ent9 ent10)))
(assert (not (and reac1 (not dir1) reac5 dir5 reac7 (not dir7) reac8 dir8 reac10 (not dir10) ent1 ent3 ent6 ent9 ent10)))
(assert (not (and reac0 dir0 reac5 (not dir5) reac6 dir6 reac8 dir8 reac9 (not dir9) ent0 ent1 ent2 ent9 ent10)))
(assert (not (and reac2 dir2 reac5 (not dir5) reac7 dir7 reac8 dir8 reac9 (not dir9) ent0 ent1 ent6 ent9 ent10)))
(assert (not (and reac3 dir3 reac5 (not dir5) reac7 dir7 reac8 dir8 reac9 (not dir9) ent0 ent1 ent6 ent9 ent10)))
(assert (not (and reac1 dir1 reac4 dir4 reac6 (not dir6) reac9 (not dir9) reac10 dir10 ent0 ent3 ent4 ent9 ent10)))
(assert (not (and reac1 dir1 reac4 dir4 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent1 ent3 ent4 ent9 ent10)))
(assert (not (and reac1 dir1 reac8 (not dir8) reac10 dir10 reac11 (not dir11) reac12 dir12 ent0 ent1 ent3 ent10 ent12)))
(assert (not (and reac1 dir1 reac5 dir5 reac7 (not dir7) reac8 (not dir8) reac10 dir10 ent0 ent1 ent3 ent9 ent10)))
(assert (not (and reac4 (not dir4) reac5 dir5 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent1 ent3 ent4 ent9 ent10)))
(assert (not (and reac1 dir1 reac5 dir5 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent1 ent3 ent4 ent9 ent10)))
(assert (not (and reac0 dir0 reac5 (not dir5) reac6 dir6 reac11 (not dir11) reac12 dir12 ent0 ent1 ent2 ent9 ent12)))
(assert (not (and reac1 dir1 reac2 dir2 reac3 (not dir3) reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent12)))
(assert (not (and reac1 dir1 reac2 dir2 reac3 (not dir3) reac5 (not dir5) reac6 dir6 ent1 ent3 ent4 ent6 ent9)))
(assert (not (and reac1 (not dir1) reac3 dir3 reac4 (not dir4) reac6 (not dir6) reac7 dir7 ent0 ent3 ent4 ent6 ent9)))
(assert (not (and reac1 (not dir1) reac2 (not dir2) reac3 dir3 reac6 (not dir6) reac7 dir7 ent0 ent3 ent4 ent6 ent9)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac4 (not dir4) reac5 (not dir5) reac6 dir6 ent1 ent3 ent4 ent6 ent9)))
(assert (not (and reac0 dir0 reac2 dir2 reac3 (not dir3) reac5 (not dir5) reac6 dir6 ent0 ent1 ent2 ent6 ent9)))
(assert (not (and reac2 dir2 reac5 (not dir5) reac7 dir7 reac11 (not dir11) reac12 dir12 ent0 ent1 ent6 ent9 ent12)))
(assert (not (and reac0 (not dir0) reac2 dir2 reac5 (not dir5) reac6 (not dir6) reac7 dir7 ent0 ent1 ent2 ent6 ent9)))
(assert (not (and reac3 dir3 reac5 (not dir5) reac7 dir7 reac11 (not dir11) reac12 dir12 ent0 ent1 ent6 ent9 ent12)))
(assert (not (and reac4 dir4 reac5 (not dir5) reac9 dir9 reac10 (not dir10) reac11 (not dir11) reac12 dir12 ent0 ent1 ent3 ent9 ent10 ent12)))
(assert (not (and reac4 dir4 reac7 (not dir7) reac8 dir8 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent9 ent10 ent12)))
(assert (not (and reac2 dir2 reac5 (not dir5) reac6 (not dir6) reac7 dir7 reac9 (not dir9) reac10 dir10 ent0 ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac4 (not dir4) reac7 dir7 reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent9 ent12)))
(assert (not (and reac0 (not dir0) reac1 dir1 reac4 dir4 reac6 (not dir6) reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent9 ent12)))
(assert (not (and reac1 dir1 reac3 dir3 reac4 dir4 reac6 (not dir6) reac8 dir8 reac9 (not dir9) ent0 ent3 ent4 ent6 ent9 ent10)))
(assert (not (and reac0 (not dir0) reac1 dir1 reac4 dir4 reac6 (not dir6) reac8 (not dir8) reac9 dir9 ent0 ent1 ent2 ent3 ent9 ent10)))
(assert (not (and reac0 (not dir0) reac1 dir1 reac5 dir5 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent0 ent1 ent2 ent3 ent9 ent10)))
(assert (not (and reac0 (not dir0) reac1 dir1 reac4 dir4 reac6 (not dir6) reac8 (not dir8) reac10 dir10 ent0 ent1 ent2 ent3 ent9 ent10)))
(assert (not (and reac5 dir5 reac6 (not dir6) reac8 (not dir8) reac10 dir10 reac11 (not dir11) reac12 dir12 ent1 ent4 ent8 ent9 ent10 ent12)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac4 dir4 reac5 (not dir5) reac9 dir9 reac10 (not dir10) ent0 ent1 ent3 ent6 ent9 ent10)))
(assert (not (and reac0 dir0 reac1 dir1 reac5 (not dir5) reac6 dir6 reac9 (not dir9) reac10 dir10 ent0 ent1 ent2 ent3 ent9 ent10)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac5 dir5 reac6 (not dir6) reac9 (not dir9) reac10 dir10 ent0 ent1 ent4 ent6 ent9 ent10)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac8 dir8 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent10 ent12)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac9 dir9 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent10 ent12)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac9 dir9 reac10 (not dir10) reac11 (not dir11) reac12 dir12 ent0 ent1 ent4 ent6 ent10 ent12)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac5 dir5 reac6 (not dir6) reac11 (not dir11) reac12 dir12 ent0 ent1 ent4 ent6 ent9 ent12)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac5 dir5 reac6 (not dir6) reac11 (not dir11) reac12 dir12 ent1 ent4 ent6 ent8 ent9 ent12)))
(assert (not (and reac2 (not dir2) reac3 dir3 reac6 (not dir6) reac7 dir7 reac11 (not dir11) reac12 dir12 ent0 ent1 ent4 ent6 ent9 ent12)))
(assert (not (and reac2 dir2 reac3 (not dir3) reac4 (not dir4) reac5 dir5 reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent9 ent12)))
(assert (not (and reac4 (not dir4) reac5 dir5 reac6 (not dir6) reac9 (not dir9) reac10 dir10 reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent4 ent9 ent10 ent12)))
(assert (not (and reac4 (not dir4) reac6 (not dir6) reac7 dir7 reac8 (not dir8) reac10 dir10 reac11 (not dir11) reac12 dir12 ent0 ent1 ent3 ent4 ent9 ent10 ent12)))
(assert (not (and reac2 dir2 reac4 (not dir4) reac7 dir7 reac9 (not dir9) reac10 dir10 reac11 dir11 reac12 (not dir12) ent0 ent1 ent3 ent6 ent9 ent10 ent12)))
(assert (not (and reac2 dir2 reac6 (not dir6) reac7 dir7 reac9 (not dir9) reac10 dir10 reac11 dir11 reac12 (not dir12) ent0 ent1 ent4 ent6 ent9 ent10 ent12)))
(assert (not (and reac0 (not dir0) reac1 dir1 reac2 dir2 reac6 (not dir6) reac7 dir7 reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent12)))
(assert (not (and reac0 dir0 reac2 dir2 reac3 (not dir3) reac4 (not dir4) reac6 dir6 reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent12)))
(assert (not (and reac0 (not dir0) reac2 dir2 reac4 (not dir4) reac6 (not dir6) reac7 dir7 reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent12)))
(assert (not (and reac0 (not dir0) reac2 dir2 reac4 dir4 reac6 (not dir6) reac8 dir8 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent10 ent12)))
(assert (not (and reac0 (not dir0) reac3 dir3 reac4 dir4 reac6 (not dir6) reac8 dir8 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent10 ent12)))
(assert (not (and reac0 (not dir0) reac2 dir2 reac6 (not dir6) reac7 dir7 reac8 dir8 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent10 ent12)))
(assert (not (and reac0 (not dir0) reac2 dir2 reac6 (not dir6) reac7 dir7 reac9 dir9 reac10 (not dir10) reac11 dir11 reac12 (not dir12) ent0 ent1 ent2 ent3 ent6 ent9 ent10 ent12)))
(check-sat)
(get-model)

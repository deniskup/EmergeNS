(declare-const ent0 Bool)
(declare-const ent1 Bool)
(declare-const ent2 Bool)
(declare-const ent3 Bool)
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
(assert (= dir0 (< coef0 0)))
(assert (= dir1 (< coef1 0)))
(assert (= dir2 (< coef2 0)))
(assert (= dir3 (< coef3 0)))
(assert (=> reac0 (and(or ent0 ent0) ent1)))
(assert (=> reac1 (and(or ent0 ent1) ent2)))
(assert (=> reac2 (and(or ent0 ent2) ent3)))
(assert (=> reac3 (and(or ent1 ent1) ent3)))
(assert (=> (and reac1 (not dir1)) (or (not ent0) (not ent1))))
(assert (=> (and reac2 (not dir2)) (or (not ent0) (not ent2))))
(assert (=> ent0 (> (+ (ite reac0 (+ (- coef0) (- coef0)) 0)
 (ite reac1(- coef1) 0)
 (ite reac2(- coef2) 0)
 0) 0)))
(assert (=> ent1 (> (+ (ite reac0 coef0 0)
 (ite reac1(- coef1) 0)
 (ite reac3 (+ (- coef3) (- coef3)) 0)
 0) 0)))
(assert (=> ent2 (> (+ (ite reac1 coef1 0)
 (ite reac2(- coef2) 0)
 0) 0)))
(assert (=> ent3 (> (+ (ite reac2 coef2 0)
 (ite reac3 coef3 0)
 0) 0)))
(assert (= (+ (ite ent0 1 0) (ite ent1 1 0) (ite ent2 1 0) (ite ent3 1 0)) 4))
(assert (= (+ (ite reac0 1 0) (ite reac1 1 0) (ite reac2 1 0) (ite reac3 1 0)) 4))
(assert (not (and reac0 dir0 reac2 (not dir2) reac3 dir3 ent0 ent1 ent3)))
(assert (not (and reac1 (not dir1) reac2 (not dir2) reac3 dir3 ent1 ent2 ent3)))
(check-sat)
(get-model)

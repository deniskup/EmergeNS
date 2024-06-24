(declare-const conc0 Real)
(assert (and (>= conc0 0)))
(declare-const conc1 Real)
(assert (and (>= conc1 0)))
(declare-const conc2 Real)
(assert (and (>= conc2 0)))
(declare-const conc3 Real)
(assert (and (>= conc3 0)))
(declare-const conc4 Real)
(assert (and (>= conc4 0)))
(declare-const conc5 Real)
(assert (and (>= conc5 0)))
(declare-const conc6 Real)
(assert (and (>= conc6 0)))
(declare-const conc7 Real)
(assert (and (>= conc7 0)))
(declare-const conc8 Real)
(assert (and (>= conc8 0)))
(declare-const conc9 Real)
(assert (and (>= conc9 0)))
(declare-const conc10 Real)
(assert (and (>= conc10 0)))
(declare-const conc11 Real)
(assert (and (>= conc11 0)))
(declare-const conc12 Real)
(assert (and (>= conc12 0)))
(declare-const conc13 Real)
(assert (and (>= conc13 0)))
(declare-const conc14 Real)
(assert (and (>= conc14 0)))
(declare-const conc15 Real)
(assert (and (>= conc15 0)))
;	clauses for CAC B2->Bf2 Bf2->BB BB->B1+B1 B1->Bf1 Bf1->B2 
(declare-const coef3 Real);	flow of B2+Fb=Bf2
(assert (= coef3 (- (* 0.3678794503 conc11 conc1 ) (* 0.3678794503 conc14 ))))
(declare-const coef4 Real);	flow of Wb+BB=Bf2
(assert (= coef4 (- (* 0.3678794503 conc15 conc12 ) (* 0.3678794503 conc14 ))))
(declare-const coef5 Real);	flow of B1+B1=BB
(assert (= coef5 (- (* 0.3678794503 conc10 conc10 ) (* 0.3678794503 conc12 ))))
(declare-const coef10 Real);	flow of B1+Fb=Bf1
(assert (= coef10 (- (* 0.3678794503 conc10 conc1 ) (* 0.3678794503 conc13 ))))
(declare-const coef11 Real);	flow of Wb+B2=Bf1
(assert (= coef11 (- (* 0.3678794503 conc15 conc11 ) (* 0.3678794503 conc13 ))))
;	production of B1
(assert (> (+ (- coef5) (- coef5) (- coef10) 0) 0.0010000000))
;	production of B2
(assert (> (+ (- coef3) (- coef11) 0) 0.0010000000))
;	production of BB
(assert (> (+ (- coef4) coef5 0) 0.0010000000))
;	production of Bf1
(assert (> (+ coef10 coef11 0) 0.0010000000))
;	production of Bf2
(assert (> (+ coef3 coef4 0) 0.0010000000))
;	clauses for CAC A2->Af2 Af2->AA AA->A1+A1 A1->Af1 Af1->A2 
(declare-const coef0 Real);	flow of A2+Fa=Af2
(assert (= coef0 (- (* 0.3678794503 conc3 conc0 ) (* 0.3678794503 conc6 ))))
(declare-const coef1 Real);	flow of Wa+AA=Af2
(assert (= coef1 (- (* 0.3678794503 conc7 conc4 ) (* 0.3678794503 conc6 ))))
(declare-const coef2 Real);	flow of A1+A1=AA
(assert (= coef2 (- (* 0.3678794503 conc2 conc2 ) (* 0.3678794503 conc4 ))))
(declare-const coef8 Real);	flow of A1+Fa=Af1
(assert (= coef8 (- (* 0.3678794503 conc2 conc0 ) (* 0.3678794503 conc5 ))))
(declare-const coef9 Real);	flow of Wa+A2=Af1
(assert (= coef9 (- (* 0.3678794503 conc7 conc3 ) (* 0.3678794503 conc5 ))))
;	production of A1
(assert (> (+ (- coef2) (- coef2) (- coef8) 0) 0.0010000000))
;	production of A2
(assert (> (+ (- coef0) (- coef9) 0) 0.0010000000))
;	production of AA
(assert (> (+ (- coef1) coef2 0) 0.0010000000))
;	production of Af1
(assert (> (+ coef8 coef9 0) 0.0010000000))
;	production of Af2
(assert (> (+ coef0 coef1 0) 0.0010000000))
(check-sat)
(get-model)

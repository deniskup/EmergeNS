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
;	clauses for CAC a2b->a2 a2->a2b2 a2b2->ab+ab ab->a2b 
(declare-const coef0 Real);	flow of a2+b=a2b
(assert (= coef0 (- (* 0.3678794503 conc2 conc1 ) (* 0.3678794503 conc4 ))))
(declare-const coef1 Real);	flow of a2+b2=a2b2
(assert (= coef1 (- (* 0.3678794503 conc2 conc3 ) (* 0.3678794503 conc6 ))))
(declare-const coef2 Real);	flow of ab+ab=a2b2
(assert (= coef2 (- (* 0.3678794503 conc7 conc7 ) (* 0.3678794503 conc6 ))))
(declare-const coef5 Real);	flow of ab+a=a2b
(assert (= coef5 (- (* 0.3678794503 conc7 conc0 ) (* 0.3678794503 conc4 ))))
;	production of a2
(assert (> (+ (- coef0) (- coef1) 0) 0.0000000000))
;	production of a2b
(assert (> (+ coef0 coef5 0) 0.0000000000))
;	production of a2b2
(assert (> (+ coef1 coef2 0) 0.0000000000))
;	production of ab
(assert (> (+ (- coef2) (- coef2) (- coef5) 0) 0.0000000000))
;	clauses for CAC b2->a2b2 a2b2->ab+ab ab2->b2 ab->ab2 
(declare-const coef3 Real);	flow of a+b2=ab2
(assert (= coef3 (- (* 0.3678794503 conc0 conc3 ) (* 0.3678794503 conc5 ))))
(declare-const coef4 Real);	flow of ab+b=ab2
(assert (= coef4 (- (* 0.3678794503 conc7 conc1 ) (* 0.3678794503 conc5 ))))
;	production of b2
(assert (> (+ (- coef1) (- coef3) 0) 0.0000000000))
;	production of ab2
(assert (> (+ coef3 coef4 0) 0.0000000000))
;	production of a2b2
(assert (> (+ coef1 coef2 0) 0.0000000000))
;	production of ab
(assert (> (+ (- coef2) (- coef2) (- coef4) 0) 0.0000000000))
(check-sat)
(get-model)

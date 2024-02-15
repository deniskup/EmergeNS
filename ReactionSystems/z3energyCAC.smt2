
(declare-const e0 Real)
(declare-const e1 Real)
(declare-const e2 Real)

(assert (> e0 0.001))
(assert (> e1 0.001))
(assert (> e2 0.001))

(assert (forall ((c0 Real) (c1 Real) (c2 Real))
	(or
		(< c0 0.)
		(> c0 100.)
		(> (* (/ (* e0 e1) e2) c0 c1) c2)
	)
	))
(check-sat)
(get-model)

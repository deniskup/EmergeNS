(declare-const boolVar Bool)
(declare-const intVar Int)

(assert boolVar)
(assert (>= intVar 0))
(assert (or (> intVar 5) (not boolVar)))
(check-sat)
(get-model)

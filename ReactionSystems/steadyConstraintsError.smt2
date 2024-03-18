(set-option :pp.decimal true)
(set-option :pp.decimal_precision 7)
(declare-const conc1 Real)
(declare-const conc2 Real)
(declare-const conc3 Real)
(declare-const conc4 Real)
(declare-const conc5 Real)
(declare-const conc6 Real)
(declare-const conc7 Real)
(declare-const conc8 Real)
(declare-const conc9 Real)
(declare-const conc10 Real)
(declare-const conc11 Real)
(declare-const conc12 Real)
(declare-const conc13 Real)
(declare-const conc14 Real)
(declare-const conc15 Real)
(declare-const conc16 Real)
(declare-const flow1 Real)
(declare-const flow2 Real)
(declare-const flow3 Real)
(declare-const flow4 Real)
(declare-const flow5 Real)
(declare-const flow6 Real)
(declare-const flow7 Real)
(declare-const flow8 Real)
(declare-const flow9 Real)
(declare-const flow10 Real)
(declare-const flow11 Real)
(declare-const flow12 Real)
(assert (> conc1 0))
(assert (> conc2 0))
(assert (> conc3 0))
(assert (> conc4 0))
(assert (> conc5 0))
(assert (> conc6 0))
(assert (> conc7 0))
(assert (> conc8 0))
(assert (> conc9 0))
(assert (> conc10 0))
(assert (> conc11 0))
(assert (> conc12 0))
(assert (> conc13 0))
(assert (> conc14 0))
(assert (> conc15 0))
(assert (> conc16 0))
(assert (= flow1 (+ (* 0.367879 conc4 conc1) (* -1. 0.367879 conc7))))
(assert (= flow2 (+ (* 0.367879 conc8 conc5) (* -1. 0.367879 conc7))))
(assert (= flow3 (+ (* 0.367879 conc3 conc3) (* -1. 0.367879 conc5))))
(assert (= flow4 (+ (* 0.367879 conc12 conc2) (* -1. 0.367879 conc15))))
(assert (= flow5 (+ (* 0.367879 conc16 conc13) (* -1. 0.367879 conc15))))
(assert (= flow6 (+ (* 0.367879 conc11 conc11) (* -1. 0.367879 conc13))))
(assert (= flow7 (+ (* 1 conc3 conc16) (* -1. 0.00673795 conc9))))
(assert (= flow8 (+ (* 1 conc11 conc8) (* -1. 0.00673795 conc10))))
(assert (= flow9 (+ (* 0.367879 conc3 conc1) (* -1. 0.367879 conc6))))
(assert (= flow10 (+ (* 0.367879 conc8 conc4) (* -1. 0.367879 conc6))))
(assert (= flow11 (+ (* 0.367879 conc11 conc2) (* -1. 0.367879 conc14))))
(assert (= flow12 (+ (* 0.367879 conc16 conc12) (* -1. 0.367879 conc14))))
(assert (= (+ (* -1 flow1) (* -1 flow9) 0.1 (* -1. 0.1 conc1)) 0))
(assert (= (+ (* -1 flow4) (* -1 flow11) 0.1 (* -1. 0.1 conc2)) 0))
(assert (= (+ (* -2 flow3) (* -1 flow7) (* -1 flow9) 0.1 (* -1. 0.01 conc3)) 0))
(assert (= (+ (* -1 flow1) (* -1 flow10) 0.1 (* -1. 0.01 conc4)) 0))
(assert (= (+ (* -1 flow2) (* 1 flow3) 0.1 (* -1. 0.01 conc5)) 0))
(assert (= (+ (* 1 flow9) (* 1 flow10) 0.1 (* -1. 0.01 conc6)) 0))
(assert (= (+ (* 1 flow1) (* 1 flow2) 0.1 (* -1. 0.01 conc7)) 0))
(assert (= (+ (* -1 flow2) (* -1 flow8) (* -1 flow10) 0.1 (* -1. 0.01 conc8)) 0))
(assert (= (+ (* 1 flow7) 0.1 (* -1. 100 conc9)) 0))
(assert (= (+ (* 1 flow8) 0.1 (* -1. 100 conc10)) 0))
(assert (= (+ (* -2 flow6) (* -1 flow8) (* -1 flow11) 0.1 (* -1. 0.01 conc11)) 0))
(assert (= (+ (* -1 flow4) (* -1 flow12) 0.1 (* -1. 0.01 conc12)) 0))
(assert (= (+ (* -1 flow5) (* 1 flow6) 0.1 (* -1. 0.01 conc13)) 0))
(assert (= (+ (* 1 flow11) (* 1 flow12) 0.1 (* -1. 0.01 conc14)) 0))
(assert (= (+ (* 1 flow4) (* 1 flow5) 0.1 (* -1. 0.01 conc15)) 0))
(assert (= (+ (* -1 flow5) (* -1 flow7) (* -1 flow12) 0.1 (* -1. 0.01 conc16)) 0))
(check-sat)
(get-model)

(set-logic ALL)

(declare-datatypes ((Rands 3)) ((par (T1 T2 T3) ((mk-rands (r0 T1) (r1 T2) (r2 T3))))))

; *** 1- configuration ***

; w = (a + r0)*(b + r1) + (a + r0)*(c + r2) + (c + r2) + (a + r0)*(r1) + (a + r0)*(r2)
(define-fun w ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1)) (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (_ BitVec 1)
  (bvxor
    (bvxor
      (bvxor
        (bvxor
          (bvxor
            (bvand (bvxor a (r0 r)) (bvxor b (r1 r)))
            (bvand (bvxor a (r0 r)) (bvxor c (r2 r)))
          )
          c
        )
        (r2 r)
      )
      (bvand (bvxor a (r0 r)) (r1 r))
    )
    (bvand (bvxor a (r0 r)) (r2 r))
  )
)

; f = r0, r1, (b + c) * (a + r0) + c + r2 + (b' + c') * (a' + r0) + c'
(define-fun f ((a (_ BitVec 1)) (b (_ BitVec 1)) (c (_ BitVec 1))
               (ap (_ BitVec 1)) (bp (_ BitVec 1)) (cp (_ BitVec 1))
               (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))
  (mk-rands (r0 r) (r1 r)
    (bvxor
      (bvxor
        (bvxor
          (bvxor
            (bvand (bvxor b c) (bvxor a (r0 r)))
            c
          )
          (r2 r)
        )
        (bvand (bvxor bp cp) (bvxor ap (r0 r)))
      )
      cp
    )
  )
)

; *** 2- constraints ***

(assert
  (forall ((a (_ BitVec 1))
           (b (_ BitVec 1))
           (c (_ BitVec 1))
           (ap (_ BitVec 1))
           (bp (_ BitVec 1))
           (cp (_ BitVec 1))
           (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1)))
           (rp (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
    (and
      ; invariance on a, b, and c
      (= (w a b c r)
         (w ap bp cp (f a b c ap bp cp r)))

      ; bijectivity of f
      (=> (= (f a b c ap bp cp r) (f a b c ap bp cp rp))
          (= r rp))
    )
  )
)

(check-sat)

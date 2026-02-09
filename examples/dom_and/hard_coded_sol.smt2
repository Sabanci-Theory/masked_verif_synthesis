(set-logic ALL)

(declare-datatypes ((Pair 2)) ((par (T1 T2) ((mk-pair (first T1) (second T2))))))
(declare-datatypes ((Rands 3)) ((par (T1 T2 T3) ((mk-rands (r0 T1) (r1 T2) (r2 T3))))))

; *** 1- configuration ***

; w = [(a + r0) * r1, ((b + r1) * r0) + r2] = [a * r1 + r0 * r1, b * r0 + r1 * r0 + r2]
(define-fun w ((a (_ BitVec 1)) (b (_ BitVec 1)) (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (Pair (_ BitVec 1) (_ BitVec 1))
  (mk-pair (
							bvxor (bvand a (r1 r)) (bvand (r0 r) (r1 r))
					 )
					 (
							bvxor (bvand b (r0 r)) (bvxor (bvand (r0 r) (r1 r)) (r2 r))
					 )
  )
)

; f | ap = 0 => a + r0, r1, ((b + r1) * r0) + r2 + ((bp + r1) * (a + r0))
;   | ap = 1 => 1 + a + r0, r1, ((b + r1) * r0) + r2 + ((bp + r1) * (1 + a + r0))
(define-fun f ((a (_ BitVec 1)) (b (_ BitVec 1)) (ap (_ BitVec 1)) (bp (_ BitVec 1)) (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))
  (ite (= ap #b0)
    (mk-rands (bvxor a (r0 r)) (r1 r) (bvxor (bvxor (bvand (bvxor b (r1 r)) (r0 r)) (r2 r)) (bvand (bvxor bp (r1 r)) (bvxor a (r0 r)))))
    (mk-rands (bvxor #b1 (bvxor a (r0 r))) (r1 r) (bvxor (bvxor (bvand (bvxor b (r1 r)) (r0 r)) (r2 r)) (bvand (bvxor bp (r1 r)) (bvxor #b1 (bvxor a (r0 r))))))
  )
)

(define-fun f0 ((a (_ BitVec 1)) (b (_ BitVec 1)) (ap (_ BitVec 1)) (bp (_ BitVec 1)) (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (_ BitVec 1)
  (ite (= ap #b0)
    (bvxor a (r0 r))
    (bvxor #b1 (bvxor a (r0 r)))
  )
)

(define-fun f1 ((a (_ BitVec 1)) (b (_ BitVec 1)) (ap (_ BitVec 1)) (bp (_ BitVec 1)) (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
  (_ BitVec 1)
  (r1 r)
)

; *** 2- constraints ***
(assert
  (forall ((a (_ BitVec 1))
           (b (_ BitVec 1))
           (ap (_ BitVec 1))
           (bp (_ BitVec 1))
           (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1)))
           (rp (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
    (and
      ; invariance on a and b
      (= (w a b r)
         (w ap bp (f a b ap bp r)))

      ; bijectivity of f
      (=> (= (f a b ap bp r) (f a b ap bp rp))
          (= r rp))
    )
  )
)

(assert
  (forall ((a (_ BitVec 1))
           (b (_ BitVec 1))
           (ap (_ BitVec 1))
           (bp (_ BitVec 1))
           (r (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1)))
           (rp (Rands (_ BitVec 1) (_ BitVec 1) (_ BitVec 1))))
    (and
      ; invariance on a and b
      (= (w a b r)
         (w ap bp 
          (mk-rands
            (f0 a b ap bp r)
            (f1 a b ap bp r) 
            (bvxor (bvxor (bvand (bvxor b (r1 r)) (r0 r)) (r2 r)) (bvand (bvxor bp (f1 a b ap bp r)) (f0 a b ap bp r)))
          )
         )
      )

      ; bijectivity of f
      (=> 
        (and 
          (= (f0 a b ap bp r) (f0 a b ap bp rp))
          (= (f1 a b ap bp r) (f1 a b ap bp rp))
        )
        (= r rp)
      )
    )
  )
)

(check-sat)

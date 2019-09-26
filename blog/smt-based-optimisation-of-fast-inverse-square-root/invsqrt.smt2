(declare-const magic (_ BitVec 32)) ; magic number used in hack

; Auxiliary functions to keep notation short
(define-fun f0.5 () Float32
    ((_ to_fp 8 24) RNE 0.5)
)
(define-fun f1.5 () Float32
    ((_ to_fp 8 24) RNE 1.5)
)

; Note that the input's (%0) bitvector representation (%2) is not computed in the characterisation of Q_rsqrt,
; but expected to be passed as additional argument since there is no _function_ for reinterpreting floats as bitvectors.
; Therefore, we _relate_ b and f outside of Q_rsqrt (asserted below)
(define-fun Q_rsqrt ((%0 Float32) (%2 (_ BitVec 32))) Float32
    (let ((%3 (bvashr %2 (_ bv1 32)))) ; %3 = ashr i32 %2, 1
    (let ((%4 (bvsub magic %3)))       ; %4 = sub nsw i32 1597463007, %3 // magic instead of 0x5F3759DF
    (let ((%5 ((_ to_fp 8 24) %4)))    ; %5 = bitcast i32 %4 to float
    (let ((%6 (fp.mul RNE %0 f0.5)))   ; %6 = fmul float %0, 5.000000e-01
    (let ((%7 (fp.mul RNE %6 %5)))     ; %7 = fmul float %6, %5
    (let ((%8 (fp.mul RNE %7 %5)))     ; %8 = fmul float %7, %5
    (let ((%9 (fp.sub RNE f1.5 %8)))   ; %9 = fsub float 1.500000e+00, %8
    (let ((%10 (fp.mul RNE %9 %5)))    ; %10 = fmul float %9, %5
        %10                            ; ret float %10
    ))))))))
)

; Auxiliary function to keep notation of 1.0f short
(define-fun f1.0 () Float32
    ((_ to_fp 8 24) RNE 1)
)

(define-fun relErr ((%0 Float32) (%1 Float32)) Float32
    (let ((%3 (fp.mul RNE %0 %1)))     ; %3 = fmul float %0, %1
    (let ((%4 (fp.sub RNE f1.0 %3)))   ; %4 = fsub float 1.000000e+00, %3
    (let ((%5 (fp.abs %4)))            ; %5 = tail call float @llvm.fabs.f32(float %4)
        %5                             ; ret float %5
    )))
)

; Test whether characterisation yields the same values as the actual executable
(push)
    (echo "===========[ Test encoding ]===========")
    (assert (= magic #x5F3759DF))     ; original magic number

    (declare-const f Float32)         ; input float
    (declare-const b (_ BitVec 32))   ; input float's bitvector representation (asserted below)
    (assert (= ((_ to_fp 8 24) b) f)) ; %3 = bitcast float %0 to i32 // originally in Q_rsqrt

    (assert (= b #x016EB3C0))         ; worst float/bit-string for that magic number
    (check-sat)

    (echo "f (should be 0x016EB3C0):")
    (eval f)
    (eval (= f ((_ to_fp 8 24) #x016EB3C0)))

    (echo "")
    (echo "fSqrt (should be 0x20773327):")
    (eval (fp.sqrt RNE f))
    (eval (=
        (fp.sqrt RNE f)
        ((_ to_fp 8 24) #x20773327))
    )

    (echo "")
    (echo "fFast (should be 0x5E84530F):")
    (eval (Q_rsqrt f b))
    (eval (=
        (Q_rsqrt f b)
        ((_ to_fp 8 24) #x5E84530F))
    )

    (echo "")
    (echo "relErr (should be 0x3AE5B000):")
    (eval (relErr (fp.sqrt RNE f) (Q_rsqrt f b)))
    (eval (=
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) #x3AE5B000))
    )
(pop)

; Does the approximation really "work" for all floats?
(push)
    (echo "")
    (echo "======[ Correct for all floats? ]======")
    (assert (= magic #x5F3759DF))      ; original magic number

    (declare-const f Float32)          ; input float
    (declare-const b (_ BitVec 32))    ; input float's bitvector representation (asserted below)
    (assert (= ((_ to_fp 8 24) b) f))  ; %3 = bitcast float %0 to i32 // originally in Q_rsqrt

    ; Let the approximation be correct, if the relative error never exceeds 0.01 (1% deviation)
    (assert (fp.gt
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) RNE 0.01)
    ))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)

        (echo "")
    (echo "===[ When excluding +/- infinity? ]====")
    (assert (not (fp.isInfinite f)))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)

    (echo "")
    (echo "==[ When also excluding +/- zero? ]====")
    (assert (not (fp.isZero f)))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)

    (echo "")
    (echo "==[ When also excluding subnormals? ]==")
    (assert (not (fp.isSubnormal f)))
    (check-sat)

    (echo "UNSAT means that no violation is possible")
    (echo "For normal floats the relative error stays below 1%")
(pop)

; Quake checks for the result becoming NaN -- can this really happen?
(push)
    (assert (= magic #x5F3759DF))      ; original magic number

    (declare-const f Float32)          ; input float
    (declare-const b (_ BitVec 32))    ; input float's bitvector representation (asserted below)
    (assert (= ((_ to_fp 8 24) b) f))  ; %3 = bitcast float %0 to i32 // originally in Q_rsqrt

    (assert (fp.isNormal f))           ; only consider normal floats

    (echo "")
    (echo "======[ Can the result be NaN? ]=======")
    (assert (fp.isNaN (relErr (fp.sqrt RNE f) (Q_rsqrt f b))))
    (check-sat)

    (echo "SAT means that it can")
    (echo "Problematic float:")
    (eval f)
    (eval (fp.to_real f))

    (echo "")
    (echo "===[ NaN if input is non-negative? ]===")
    (assert (not (fp.isNegative f )))
    (check-sat)
    (echo "UNSAT means that NaN cannot occur")
(pop)

; What is the tightest/smallest bound for the relative error? Could be better than 1%
(push)
    (assert (= magic #x5f3759df))     ; original magic number

    (declare-const f Float32)         ; input float
    (declare-const b (_ BitVec 32))   ; input float's bitvector representation (asserted below)
    (assert (= ((_ to_fp 8 24) b) f)) ; %3 = bitcast float %0 to i32 // originally in Q_rsqrt

    (assert (fp.isNormal f))          ; only consider normal floats
    (assert (not (fp.isNegative f ))) ; only consider non-negative floats

    ; Automated minimisation via (minimize (relErr (fp.sqrt RNE f) (Q_rsqrt f b))) not supported for FP,
    ; but can be done manually by iteratively refining the bound for relErr (e.g. via binary search)

    ; Try with 0.1%, i.e. 0.001
    (echo "")
    (echo "===[ Max. relative error <= 0.001? ]===")
    (assert (fp.gt
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) RNE 0.001)
    ))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)
    (echo "relErr:")
    (eval (fp.to_real (relErr (fp.sqrt RNE f) (Q_rsqrt f b))))
    (eval (relErr (fp.sqrt RNE f) (Q_rsqrt f b)))

    ; Try with 0.15%, i.e. 0.0015
    (echo "")
    (echo "==[ Max. relative error <= 0.0015? ]===")
    (assert (fp.gt
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) RNE 0.0015)
    ))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)
    (echo "relErr:")
    (eval (fp.to_real (relErr (fp.sqrt RNE f) (Q_rsqrt f b))))
    (eval (relErr (fp.sqrt RNE f) (Q_rsqrt f b)))

    ; Several iterations later ... try with 0.0017523764399811625 (0x3AE5AFFF)
    (echo "")
    (echo "=[ Max. relative error <= 0.00175..? ]=")
    (assert (fp.gt
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) #x3AE5AFFF)
    ))
    (check-sat)

    (echo "SAT means that a violation is possible")
    (echo "Problematic float:")
    (eval f)
    (eval b)
    (echo "relErr:")
    (eval (fp.to_real (relErr (fp.sqrt RNE f) (Q_rsqrt f b))))
    (eval (relErr (fp.sqrt RNE f) (Q_rsqrt f b)))
    (echo "In fact, this float yields the maximal relative error")
    (echo "The constraints for achieving a greater relative error are UNSAT")

    ; Prove that picking anything above 0.0017523765563964844 (0x3AE5B000) renders the constraints UNSAT
    (echo "")
    (echo "====[ Check with increased bound ]=====")
    (assert (fp.gt
        (relErr (fp.sqrt RNE f) (Q_rsqrt f b))
        ((_ to_fp 8 24) #x3AE5B000)
    ))
    (check-sat)

    (echo "The relative error can indeed not grow further")
    (echo "The maximal relative error is exactly 0.0017523765563964844 (0x3AE5B000)")
(pop)

; Is there a "better" magic number, causing a smaller maximal relative error?
(push)
    (echo "")
    (echo "==[ Is there a better magic number? ]==")
    (assert (forall ((f Float32) (b (_ BitVec 32)))
        (=>
            (and
                (fp.isNormal f)          ; only consider normal floats
                (not (fp.isNegative f )) ; only consider non-negative floats
                (= ((_ to_fp 8 24) b) f) ; %3 = bitcast float %0 to i32 // in Q_rsqrt
            )
            (let ((fSqrt (fp.sqrt RNE f)) (fFast (Q_rsqrt f b)))
                (fp.lt
                    (relErr fSqrt fFast)
                    ((_ to_fp 8 24) RNE 0.001752) ; Original magic number had a max. rel. err of ~0.001752
                )
            )
        )
    ))
    (check-sat)

    (echo "")
    (echo "SAT means that a better one exists (max rel err < 0.001752)")
    (echo "magic:")
    (eval magic)

    ; Is there a even better one? The best one can again be found by iteratively refining the bound.
	(echo "")
    (echo "=[ Magic with rel. err < 0x3AE58E00? ]=")
    (assert (forall ((f Float32) (b (_ BitVec 32)))
        (=>
            (and
                (fp.isNormal f)          ; only consider normal floats
                (not (fp.isNegative f )) ; only consider non-negative floats
                (= ((_ to_fp 8 24) b) f) ; %3 = bitcast float %0 to i32 // in Q_rsqrt
            )
            (let ((fSqrt (fp.sqrt RNE f)) (fFast (Q_rsqrt f b)))
                (fp.lt
                    (relErr fSqrt fFast)
                    ((_ to_fp 8 24) #x3AE58E00) ; max. rel. err < 0.0017513632774353027
                )
            )
        )
    ))
    (check-sat)

    (echo "")
    (echo "SAT means that a better one exists (max rel err < 0.00175133)")
    (echo "magic:")
    (eval magic)

    (echo "This is in fact an optimal constant, minimising the maximal relative error to 0.0017513036.. (0x3AE58C00)")
    (echo "Decreasing the bound will render the constraints UNSAT")

    ; Prove that there is none to drive the maximal relative error below 0.0017513036.. (0x3AE58C00)
    (echo "")
    (echo "=[ Magic with rel. err < 0x3AE58C00? ]=")
    (assert (forall ((f Float32) (b (_ BitVec 32)))
        (=>
            (and
                (fp.isNormal f)          ; only consider normal floats
                (not (fp.isNegative f )) ; only consider non-negative floats
                (= ((_ to_fp 8 24) b) f) ; %3 = bitcast float %0 to i32 // in Q_rsqrt
            )
            (let ((fSqrt (fp.sqrt RNE f)) (fFast (Q_rsqrt f b)))
                (fp.lt
                    (relErr fSqrt fFast)
                    ((_ to_fp 8 24) #x3AE58C00) ; max. rel. err < 0.0017513036727905273
                )
            )
        )
    ))
    (check-sat)
    (echo "")
    (echo "For no magic number is the maximal relative error below 0.0017513036.. (0x3AE58C00)")
(pop)

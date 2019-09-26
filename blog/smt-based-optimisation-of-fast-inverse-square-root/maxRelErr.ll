; ModuleID = 'maxRelErr.c'
source_filename = "maxRelErr.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@magic = dso_local local_unnamed_addr constant i32 1597463007, align 4
@.str = private unnamed_addr constant [29 x i8] c"arch: %zu-bit\0Amagic: 0x%08X\0A\00", align 1
@.str.1 = private unnamed_addr constant [23 x i8] c"worst: 0x%08X (%.12f)\0A\00", align 1
@.str.2 = private unnamed_addr constant [23 x i8] c"fSqrt: 0x%08X (%.12f)\0A\00", align 1
@.str.3 = private unnamed_addr constant [23 x i8] c"fFast: 0x%08X (%.12f)\0A\00", align 1
@.str.4 = private unnamed_addr constant [27 x i8] c"maxRelErr: 0x%08X (%.19f)\0A\00", align 1

; Function Attrs: norecurse nounwind readnone sspstrong uwtable
define dso_local float @Q_rsqrt(float) local_unnamed_addr #0 {
  %2 = bitcast float %0 to i32
  %3 = ashr i32 %2, 1
  %4 = sub nsw i32 1597463007, %3
  %5 = bitcast i32 %4 to float
  %6 = fmul float %0, 5.000000e-01
  %7 = fmul float %6, %5
  %8 = fmul float %7, %5
  %9 = fsub float 1.500000e+00, %8
  %10 = fmul float %9, %5
  ret float %10
}

; Function Attrs: nounwind readnone sspstrong uwtable
define dso_local float @relErr(float, float) local_unnamed_addr #1 {
  %3 = fmul float %0, %1
  %4 = fsub float 1.000000e+00, %3
  %5 = tail call float @llvm.fabs.f32(float %4)
  ret float %5
}

; Function Attrs: nounwind sspstrong uwtable
define dso_local float @findWorst() local_unnamed_addr #2 {
  br label %1

; <label>:1:                                      ; preds = %26, %0
  %2 = phi i32 [ 0, %0 ], [ %29, %26 ]
  %3 = phi float [ 0.000000e+00, %0 ], [ %27, %26 ]
  %4 = phi float [ 0.000000e+00, %0 ], [ %28, %26 ]
  %5 = bitcast i32 %2 to float
  %6 = tail call i32 @__fpclassifyf(float %5) #6
  %7 = icmp ne i32 %6, 4
  %8 = fcmp ult float %5, 0.000000e+00
  %9 = or i1 %8, %7
  br i1 %9, label %26, label %10

; <label>:10:                                     ; preds = %1
  %11 = tail call float @sqrtf(float %5) #4
  %12 = ashr i32 %2, 1
  %13 = sub nsw i32 1597463007, %12
  %14 = bitcast i32 %13 to float
  %15 = fmul float %5, 5.000000e-01
  %16 = fmul float %15, %14
  %17 = fmul float %16, %14
  %18 = fsub float 1.500000e+00, %17
  %19 = fmul float %18, %14
  %20 = fmul float %19, %11
  %21 = fsub float 1.000000e+00, %20
  %22 = tail call float @llvm.fabs.f32(float %21) #7
  %23 = fcmp ogt float %22, %4
  %24 = select i1 %23, float %5, float %3
  %25 = select i1 %23, float %22, float %4
  br label %26

; <label>:26:                                     ; preds = %10, %1
  %27 = phi float [ %3, %1 ], [ %24, %10 ]
  %28 = phi float [ %4, %1 ], [ %25, %10 ]
  %29 = add i32 %2, 1
  %30 = icmp eq i32 %29, 0
  br i1 %30, label %31, label %1

; <label>:31:                                     ; preds = %26
  ret float %27
}

; Function Attrs: nounwind readnone
declare i32 @__fpclassifyf(float) local_unnamed_addr #3

; Function Attrs: nounwind sspstrong uwtable
define dso_local i32 @main() local_unnamed_addr #2 {
  %1 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([29 x i8], [29 x i8]* @.str, i64 0, i64 0), i64 64, i32 1597463007)
  br label %2

; <label>:2:                                      ; preds = %27, %0
  %3 = phi i32 [ 0, %0 ], [ %30, %27 ]
  %4 = phi float [ 0.000000e+00, %0 ], [ %28, %27 ]
  %5 = phi float [ 0.000000e+00, %0 ], [ %29, %27 ]
  %6 = bitcast i32 %3 to float
  %7 = tail call i32 @__fpclassifyf(float %6) #6
  %8 = icmp ne i32 %7, 4
  %9 = fcmp ult float %6, 0.000000e+00
  %10 = or i1 %9, %8
  br i1 %10, label %27, label %11

; <label>:11:                                     ; preds = %2
  %12 = tail call float @sqrtf(float %6) #4
  %13 = ashr i32 %3, 1
  %14 = sub nsw i32 1597463007, %13
  %15 = bitcast i32 %14 to float
  %16 = fmul float %6, 5.000000e-01
  %17 = fmul float %16, %15
  %18 = fmul float %17, %15
  %19 = fsub float 1.500000e+00, %18
  %20 = fmul float %19, %15
  %21 = fmul float %20, %12
  %22 = fsub float 1.000000e+00, %21
  %23 = tail call float @llvm.fabs.f32(float %22) #7
  %24 = fcmp ogt float %23, %5
  %25 = select i1 %24, float %6, float %4
  %26 = select i1 %24, float %23, float %5
  br label %27

; <label>:27:                                     ; preds = %11, %2
  %28 = phi float [ %4, %2 ], [ %25, %11 ]
  %29 = phi float [ %5, %2 ], [ %26, %11 ]
  %30 = add i32 %3, 1
  %31 = icmp eq i32 %30, 0
  br i1 %31, label %32, label %2

; <label>:32:                                     ; preds = %27
  %33 = bitcast float %28 to i32
  %34 = fpext float %28 to double
  %35 = tail call float @sqrtf(float %28) #4
  %36 = bitcast float %35 to i32
  %37 = ashr i32 %33, 1
  %38 = sub nsw i32 1597463007, %37
  %39 = bitcast i32 %38 to float
  %40 = fmul float %28, 5.000000e-01
  %41 = fmul float %40, %39
  %42 = fmul float %41, %39
  %43 = fsub float 1.500000e+00, %42
  %44 = fmul float %43, %39
  %45 = bitcast float %44 to i32
  %46 = fmul float %44, %35
  %47 = fsub float 1.000000e+00, %46
  %48 = tail call float @llvm.fabs.f32(float %47) #7
  %49 = bitcast float %48 to i32
  %50 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.1, i64 0, i64 0), i32 %33, double %34)
  %51 = fpext float %35 to double
  %52 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.2, i64 0, i64 0), i32 %36, double %51)
  %53 = fpext float %44 to double
  %54 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([23 x i8], [23 x i8]* @.str.3, i64 0, i64 0), i32 %45, double %53)
  %55 = fpext float %48 to double
  %56 = tail call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([27 x i8], [27 x i8]* @.str.4, i64 0, i64 0), i32 %49, double %55)
  ret i32 0
}

; Function Attrs: nounwind
declare i32 @printf(i8* nocapture readonly, ...) local_unnamed_addr #4

; Function Attrs: nounwind readnone speculatable
declare float @llvm.fabs.f32(float) #5

declare float @sqrtf(float) local_unnamed_addr

attributes #0 = { norecurse nounwind readnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind readnone sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind sspstrong uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind readnone speculatable }
attributes #6 = { nounwind readnone }
attributes #7 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{i32 7, !"PIC Level", i32 2}
!2 = !{i32 7, !"PIE Level", i32 2}
!3 = !{!"clang version 8.0.1 (tags/RELEASE_801/final)"}

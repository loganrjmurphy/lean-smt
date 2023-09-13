(set-logic UFLRA)
(declare-sort Point)
(declare-sort Line)
(declare-sort Circle)

(declare-fun Between (Point Point Point) Bool)
(declare-fun OnL (Point Line) Bool)
(declare-fun OnC (Point Circle) Bool)
(declare-fun Inside (Point Circle) Bool)
(declare-fun Centre (Point Circle) Bool)
(declare-fun SameSide (Point Point Line) Bool)
(declare-fun IntersectsLL (Line Line) Bool)
(declare-fun IntersectsLC (Line Circle) Bool)
(declare-fun IntersectsCC (Circle Circle) Bool)


(declare-fun SegmentPP (Point Point) Real)
(declare-fun AnglePPP (Point Point Point) Real)
(declare-fun AreaPPP (Point Point Point) Real)
(declare-const RightAngle Real)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Diagrammatic axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; two_points_determine_line
(assert (forall ((a Point) (b Point) (L Line) (M Line)) (! (=> (and (not (= a b)) (OnL a L) (OnL b L) (OnL a M) (OnL b M) ) (= L M) ) :pattern ((OnL a L) (OnL b L) (OnL a M) (OnL b M)) ) ))

; center_unique
(assert (forall ((a Point) (b Point) (alpha Circle)) (=> (and (Centre a alpha) (Centre b alpha) ) (= a b) ) ))

; center_inside_circle
(assert (forall ((a Point) (alpha Circle)) (=> (Centre a alpha) (Inside a alpha) ) ))

; inside_not_on_circle
(assert (forall ((a Point) (alpha Circle)) (=> (Inside a alpha) (not (OnC a alpha)) ) ))

; between_symm
(assert (forall ((a Point) (b Point) (c Point)) (=> (Between a b c) (and (Between c b a) (not (= a b)) (not (= a c)) (not (Between b a c)) ) ) ))

; between_same_line_c
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (Between a b c) (OnL a L) (OnL b L) ) (OnL c L) ) ))

; between_same_line_b
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (Between a b c) (OnL a L) (OnL c L) ) (OnL b L) ) ))

; between_trans_in
(assert (forall ((a Point) (b Point) (c Point) (d Point)) (=> (and (Between a b c) (Between a d b) ) (Between a d c) ) ))

; between_trans_out
(assert (forall ((a Point) (b Point) (c Point) (d Point)) (=> (and (Between a b c) (Between b c d) ) (Between a b d) ) ))

; between_points
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (not (= a b)) (not (= b c)) (not (= c a)) (OnL a L) (OnL b L) (OnL c L) ) (or (Between a b c) (Between b a c) (Between a c b) ) ) ))

; between_not_trans
(assert (forall ((a Point) (b Point) (c Point) (d Point)) (=> (and (Between a b c) (Between a b d) ) (not (Between c b d)) ) ))

; same_side_refl
(assert (forall ((a Point) (L Line)) (=> (not (OnL a L)) (SameSide a a L) ) ))

; same_side_symm
(assert (forall ((a Point) (b Point) (L Line)) (=> (SameSide a b L) (SameSide b a L) ) ))

; same_side_not_on_line
(assert (forall ((a Point) (b Point) (L Line)) (! (=> (SameSide a b L) (not (OnL a L)) ) :pattern ((SameSide a b L)) ) ))

; same_side_trans
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (SameSide a b L) (SameSide a c L) ) (SameSide b c L) ) ))

; same_side_pigeon_hole
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (not (OnL a L)) (not (OnL b L)) (not (OnL c L)) ) (or (SameSide a b L) (SameSide a c L) (SameSide b c L) ) ) ))

; pasch_1
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (Between a b c) (SameSide a c L) ) (SameSide a b L) ) ))

; pasch_2
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (Between a b c) (OnL a L) (not (OnL b L)) ) (SameSide b c L) ) ))

; pasch_3
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (Between a b c) (OnL b L) ) (not (SameSide a c L)) ) ))

; pasch_4
(assert (forall ((a Point) (b Point) (c Point) (L Line) (M Line)) (=> (and (not (= L M)) (OnL b L) (OnL b M) (not (= a c)) (OnL a M) (OnL c M) (not (= a b)) (not (= c b)) (not (SameSide a c L)) ) (Between a b c) ) ))

; triple_incidence_1
(assert (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point)) (! (=> (and (OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) (SameSide c d L) (SameSide b c N) ) (not (SameSide b d M)) ) :pattern ((OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) (SameSide c d L) (SameSide b c N)) ) ))

; triple_incidence_2
(assert (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point)) (! (=> (and (OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) (SameSide c d L) (not (SameSide b d M)) (not (OnL d M)) (not (= b a)) ) (SameSide b c N) ) :pattern ((OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) (SameSide c d L)) ) ))

; triple_incidence_3
(assert (forall ((L Line) (M Line) (N Line) (a Point) (b Point) (c Point) (d Point) (e Point)) (! (=> (and (OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) (SameSide c d L) (SameSide b c N) (SameSide d e M) (SameSide c e N) ) (SameSide c e L) )))) ;:pattern ((OnL a L) (OnL a M) (OnL a N) (OnL b L) (OnL c M) (OnL d N) e) ) ))


; circle_line_intersections
(assert (forall ((a Point) (b Point) (c Point) (L Line) (alpha Circle)) (=> (and (OnL a L) (OnL b L) (OnL c L) (Inside a alpha) (OnC b alpha) (OnC c alpha) (not (= b c)) ) (Between b a c) ) ))

; circle_points_between
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (=> (and (or (Inside a alpha) (OnC a alpha) ) (or (Inside b alpha) (OnC b alpha) ) (Between a c b) ) (Inside c alpha) ) ))

; circle_points_extend
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (=> (and (or (Inside a alpha) (OnC a alpha) ) (not (Inside c alpha)) (Between a c b) ) (and (not (Inside b alpha)) (not (OnC b alpha)) ) ) ))

; circles_intersections_diff_side
(assert (forall ((a Point) (b Point) (c Point) (d Point) (alpha Circle) (beta Circle) (L Line)) (! (=> (and (not (= alpha beta)) (OnC c alpha) (OnC c beta) (OnC d alpha) (OnC d beta) (not (= c d)) (Centre a alpha) (Centre b beta) (OnL a L) (OnL b L)  ) (not (SameSide c d L)) ) :pattern ((OnC c alpha) (OnC c beta) (OnC d alpha) (OnC d beta) (Centre b beta) (OnL a L) (OnL b L)) ) ))

; intersection_lines
(assert (forall ((a Point) (b Point) (L Line) (M Line)) (=> (and (not (OnL a L)) (not (OnL b L)) (not (SameSide a b L)) (OnL a M) (OnL b M) ) (IntersectsLL L M) ) ))

; intersection_lines_common_point
(assert (forall ((a Point) (L Line) (M Line)) (=> (and (OnL a L) (OnL a M) (not (= L M)) ) (IntersectsLL L M) ) ))

; parallel_line_unique
(assert (forall ((a Point) (L Line) (M Line) (N Line)) (=> (and (not (OnL a L)) (OnL a M) (OnL a N) (not (IntersectsLL L M)) (not (IntersectsLL L N)) ) (= M N) ) ))

; intersection_symm
(assert (forall ((L Line) (M Line)) (=> (IntersectsLL L M) (IntersectsLL M L) ) ))

; intersection_circle_line_1
(assert (forall ((a Point) (b Point) (alpha Circle) (L Line))  (! (=> (and (or (OnC a alpha) (Inside a alpha) ) (or (OnC b alpha) (Inside b alpha) ) (not (OnL a L)) (not (OnL b L)) (not (SameSide a b L)) ) (IntersectsLC L alpha) )) ))
;  :pattern ((OnC a alpha) (Inside a alpha) )
  
; intersection_circle_line_2
(assert (forall ((a Point) (alpha Circle) (L Line)) (! (=> (and (Inside a alpha) (OnL a L) ) (IntersectsLC L alpha) ) :pattern ((Inside a alpha) (OnL a L)) ) )) 

; intersection_circle_circle_1
(assert (forall ((a Point) (b Point) (alpha Circle) (beta Circle)) (! (=> (and (or   (OnC a alpha)   (Inside a alpha) ) (or   (OnC b alpha)   (Inside b alpha) ) (Inside a beta) (not (Inside b beta)) (not (OnC b beta)) ) (IntersectsCC alpha beta) ) :pattern ((Inside a beta) (Inside b alpha)) ) ))

; intersection_circle_circle_2
(assert (forall ((a Point) (b Point) (alpha Circle) (beta Circle)) (! (=> (and (OnC a alpha) (Inside b alpha) (Inside a beta) (OnC b beta) ) (IntersectsCC alpha beta) ) :pattern ((OnC a alpha) (Inside b alpha) (Inside a beta) (OnC b beta)) ) ))

; parallelogram_same_side
(assert (forall ((a Point) (b Point) (c Point) (d Point) (AB Line) (CD Line) (AC Line) (BD Line)) (! (=> (and (OnL a AB) (OnL b AB) (OnL c CD) (OnL d CD) (OnL a AC) (OnL c AC) (not (= b d)) (OnL b BD) (OnL d BD) (SameSide c d AB) (not (IntersectsLL AC BD)) ) (and (SameSide b d AC) (SameSide a c BD) (SameSide a b CD) ) ) :pattern ((OnL a AB) (OnL b AB) (OnL a AC) (SameSide c d AB) (OnL c CD) (OnL d BD)) ) ))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Metric axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; zero_segment_if
(assert (forall ((a Point) (b Point)) (=> (= (SegmentPP a b) 0.0) (= a b) ) ))

; zero_segment_onlyif
(assert (forall ((a Point) (b Point)) (=> (= a b) (= (SegmentPP a b) 0.0) ) ))

; segment_gte_zero
(assert (forall ((a Point) (b Point)) (>= (SegmentPP a b) 0.0) ))

; segment_symm
(assert (forall ((a Point) (b Point)) (= (SegmentPP a b) (SegmentPP b a)) ))

;angle_symm
(assert (forall ((a Point) (b Point) (c Point)) (=> (and (not (= a b)) (not (= b c)) ) (= (AnglePPP a b c) (AnglePPP c b a)) ) ))

;angle_range
(assert (forall ((a Point) (b Point) (c Point)) (=> (and (not (= a b)) (not (= b c)) ) (and (>= (AnglePPP a b c) 0.0) (<= (AnglePPP a b c) (+ RightAngle RightAngle))  ) ) ))

; degenerated_area
(assert (forall ((a Point) (b Point)) (= (AreaPPP a a b) 0.0) ))

;; area_gte_zero
(assert (forall ((a Point) (b Point) (c Point)) (>= (AreaPPP a b c) 0.0) ))

; area_symm_1
(assert (forall ((a Point) (b Point) (c Point)) (= (AreaPPP a b c) (AreaPPP c a b)) ))

; area_symm_2
(assert (forall ((a Point) (b Point) (c Point)) (= (AreaPPP a b c) (AreaPPP a c b)) ))

;area_congruence
(assert (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (f Point)) (! (=> (and (= (SegmentPP a b) (SegmentPP d e)) (= (SegmentPP b c) (SegmentPP e f)) (= (SegmentPP c a) (SegmentPP f d)) (= (AnglePPP a b c) (AnglePPP d e f)) (= (AnglePPP b c a) (AnglePPP e f d)) (= (AnglePPP c a b) (AnglePPP f d e)) ) (= (AreaPPP a b c) (AreaPPP d e f)) ) :pattern ((= (SegmentPP a b) (SegmentPP d e)) (= (SegmentPP b c) (SegmentPP e f)) (= (SegmentPP c a) (SegmentPP f d)) (= (AnglePPP a b c) (AnglePPP d e f)) (= (AnglePPP b c a) (AnglePPP e f d)) (= (AnglePPP c a b) (AnglePPP f d e))) ) ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Transfer axioms
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; between_if
(assert (forall ((a Point) (b Point) (c Point)) (! (=> (Between a b c) (= (+ (SegmentPP a b) (SegmentPP b c)) (SegmentPP a c)) ) :pattern ((Between a b c)) ) ))

; between_onlyif
(assert (forall ((a Point) (b Point) (c Point)) (! (=> (and (not (= a b)) (not (= b c)) (not (= c a)) (= (+ (SegmentPP a b) (SegmentPP b c)) (SegmentPP a c)) ) (Between a b c) ) :pattern ((= (+ (SegmentPP a b) (SegmentPP b c)) (SegmentPP a c))) ) ))


; equal_circles
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle) (beta Circle)) (! (=> (and (Centre a alpha) (Centre a beta) (OnC b alpha) (OnC c beta) (= (SegmentPP a b) (SegmentPP a c)) ) (= alpha beta) ) :pattern ((Centre a alpha) (Centre a beta) (OnC b alpha) (OnC c beta) (= (SegmentPP a b) (SegmentPP a c))) ) ))

; point_on_circle_if
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (! (=> (and (Centre a alpha) (OnC b alpha) (= (SegmentPP a c) (SegmentPP a b)) ) (OnC c alpha) ) :pattern ((Centre a alpha) (= (SegmentPP a c) (SegmentPP a b))) ) ))

; point_on_circle_onlyif
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (! (=> (and (Centre a alpha) (OnC b alpha) (OnC c alpha) ) (= (SegmentPP a c) (SegmentPP a b)) ) :pattern ((Centre a alpha) (OnC b alpha) (OnC c alpha)) ) ))

; point_in_circle_if
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (! (=> (and (Centre a alpha) (OnC b alpha) (< (SegmentPP a c) (SegmentPP a b)) ) (Inside c alpha) ) :pattern ((Centre a alpha) (OnC b alpha) (< (SegmentPP a c) (SegmentPP a b))) ) ))

; point_in_circle_onlyif
(assert (forall ((a Point) (b Point) (c Point) (alpha Circle)) (! (=> (and (Centre a alpha) (OnC b alpha) (Inside c alpha) ) (< (SegmentPP a c) (SegmentPP a b)) ) :pattern ((Centre a alpha) (OnC b alpha) (Inside c alpha)) ) ))

; degenerated_angle_if
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (! (=> (and (not (= a b)) (not (= a c)) (OnL a L) (OnL b L) (OnL c L) (not (Between b a c)) ) (= (AnglePPP b a c) 0.0) ) :pattern ((OnL a L) (OnL b L) (OnL c L)) ) ))

; degenerated_angle_onlyif
(assert  (forall ((a Point) (b Point) (c Point) (L Line))  (=> (and (not (= a b)) (not (= a c)) (OnL a L) (OnL b L) (= (AnglePPP b a c) 0.0) ) (and (OnL c L) (not (Between b a c))  )  )  ))

; angle_superposition
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line)) (! (=> (and (OnL a L) (OnL b L) (not (= a b)) (not (= d a)) (SameSide c d L) (= (AnglePPP b a c) (AnglePPP b a d)) (= (SegmentPP a c) (SegmentPP a d)) ) (= c d) ) :pattern ((OnL a L) (OnL b L) (SameSide c d L) (= (AnglePPP b a c) (AnglePPP b a d)) (= (SegmentPP a c) (SegmentPP a d))) ) ))

; sum_angles_if
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line)) (! (=>  (and (OnL a L) (OnL a M) (OnL b L) (OnL c M) (not (= a b)) (not (= a c)) (not (OnL d L)) (not (OnL d M)) (not (= L M)) (= (AnglePPP b a c) (+ (AnglePPP b a d) (AnglePPP d a c))) )  (and (SameSide b d M) (SameSide c d L) ) ) :pattern ((OnL a L) (OnL a M) (OnL b L) (OnL c M) (= (AnglePPP b a c) (+ (AnglePPP b a d) (AnglePPP d a c)))) )  ))

; sum_angles_onlyif
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line)) (=> (and (OnL a L) (OnL a M) (OnL b L) (OnL c M) (not (= a b)) (not (= a c)) (not (OnL d L)) (not (OnL d M)) (not (= L M))  (SameSide b d M) (SameSide c d L)  )  (= (AnglePPP b a c) (+ (AnglePPP b a d) (AnglePPP d a c))) ) ))

; perpendicular_if
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line)) (=> (and (OnL a L) (OnL b L) (Between a c b)  (not (OnL d L))  (= (AnglePPP a c d) (AnglePPP d c b)) )  (= (AnglePPP a c d) RightAngle)  )  ))

; perpendicular_onlyif
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line)) (=> (and (OnL a L) (OnL b L) (Between a c b) (not (OnL d L)) (= (AnglePPP a c d) RightAngle) ) (= (AnglePPP a c d) (AnglePPP d c b)) ) ))

; flat_angle_onlyif
(assert (forall ((a Point) (b Point) (c Point))  (=> (Between a b c) (= (AnglePPP a b c) (+ RightAngle RightAngle) ) )  ))

; flat_angle_if
(assert (forall ((a Point) (b Point) (c Point)) (=> (and (not (= a b)) (not (= a c)) (=  (AnglePPP a b c) (+ RightAngle RightAngle) ) ) (Between a b c) ) ))

; equal_angles
(assert (forall ((a Point) (b Point) (e Point) (c Point) (L Line) (M Line)) (! (=> (and (OnL a L) (OnL b L) (OnL e L) (OnL a M) (OnL c M) (not (= c a)) (Between a b e) ) (= (AnglePPP b a c) (AnglePPP e a c)) ) :pattern ((Between a b e) (OnL a L) (OnL a M) (OnL c M) (OnL e L)) ) ));
;
; lines_intersect;
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line) (M Line) (N Line)) (! (=> (and (OnL a L) (OnL b L) (OnL b M) (OnL c M) (OnL c N) (OnL d N)  (not (= b c)) (SameSide a d M) (<   (+ (AnglePPP a b c) (AnglePPP b c d))   (+ RightAngle RightAngle) ) ) (exists ((e Point))  (and   (OnL e L)   (OnL e N)   (SameSide e a M) )  ) )))) ;  :pattern ((< (+ (AnglePPP a b c) (AnglePPP b c d)) (+ RightAngle RightAngle)) L M N) ) ))

; degenerated_area_if
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (! (=> (and (OnL a L) (OnL b L) (not (= a b)) (= (AreaPPP a b c) 0.0) )  (OnL c L) )))) ;:pattern ((= (AreaPPP a b c) 0.0) L) ) ))

; degenerated_area_onlyif
(assert (forall ((a Point) (b Point) (c Point) (L Line)) (=> (and (OnL a L) (OnL b L) (not (= a b))  (OnL c L)  )  (= (AreaPPP a b c) 0.0) ) ))

; sum_areas_if
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line)) (=> (and (OnL a L) (OnL b L) (OnL c L) (not (= a b)) (not (= a c))  (not (= b c)) (not (OnL d L)) (Between a c b) ) (= (+ (AreaPPP a c d) (AreaPPP d c b)) (AreaPPP a d b) ) ) ))

; sum_areas_onlyif
(assert (forall ((a Point) (b Point) (c Point) (d Point) (L Line)) (=> (and (OnL a L) (OnL b L) (OnL c L) (not (= a b)) (not (= a c)) (not (= b c)) (not (OnL d L)) (= (+ (AreaPPP a c d) (AreaPPP d c b)) (AreaPPP a d b) ) ) (Between a c b) ) ))

; parallelogram_area
;(assert 
;  ;(forall ((a Point) (b Point) (c Point) (d Point) (AB Line) (AC Line) (BD Line))  ; (! ;  (=>; (and
;  ;  (OnL a AB)  ; (OnL b AB) ;  (OnL a AC)  ; (OnL c AC) ;  (not (= b d))  ; (OnL b BD) ;  (OnL d BD)  ; (SameSide c d AB) ;  (not (IntersectsLL AC BD))  ; ) ;  (=  ; (+ (AreaPPP a c d) (AreaPPP a d b)) ;  (+ (AreaPPP b a c) (AreaPPP b c d))  ; ) ;  )  ; :pattern ((OnL a AB) (OnL b AB) (OnL a AC) (OnL c AC) (OnL b BD) (OnL d BD) (SameSide a c BD)) ;  ); )
;)

; sum_parallelograms_area
;(assert; (forall ((a Point) (b Point) (c Point) (d Point) (e Point) (f Point) (AB Line) (AC Line) (BD Line))
; ; (! ;  (=>  ; (and ;  (OnL a AB); (OnL b AB)  ; (OnL a AC) ;  (OnL c AC)  ; (not (= b d)) ;  (OnL b BD)  ; (OnL d BD)  ; (SameSide c d AB) ;  (not (IntersectsLL AC BD))  ;; (Between a e b) ;  (Between c f d)  ; ) ;  (=  ; (+ (AreaPPP a c f) (AreaPPP a f e) (AreaPPP e f d) (AreaPPP e d b)) ;  (+ (AreaPPP a c d) (AreaPPP a d b))  ; ) ;  )  ;  ;:pattern ((OnL a AB) (OnL b AB) (SameSide c d AB) (Between a e b) (Between c f d) AC BD) ;  ); )
;)

;; Extracted from Lean proof context

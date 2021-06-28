(*! Utilities | Environments used to track variable bindings !*)
From Coq Require Import Bool.Bool.
From Coq Require Import Lists.List.
Import ListNotations.

Section Contexts.
  Context {reg_t: Type}.
  Context {all_reg: list reg_t}.

  Context {get_pos: reg_t -> nat}.
  Context {get_size: reg_t -> nat}.
  Context {get_initial_value: reg_t -> list bool}.

  Definition initial_map : list bool :=
    (fix f (remaining_reg : list reg_t) (l : list bool) : list bool :=
      match remaining_reg with
      | nil  => l
      | h::t => f t (app (get_initial_value h) l)
      end
    ) all_reg [].

  Definition map_get (map: list bool) (reg: reg_t) : list bool :=
    firstn (get_size reg) (skipn (get_pos reg) map).

  Definition map_set (map: list bool) (reg: reg_t) (val: list bool) :=
    let pos := get_pos reg in
    (firstn pos map) ++ val ++ (skipn (pos + (get_size reg)) map).
End Contexts.

Inductive test_reg_t :=
| A    | B    | B0   | B1   | B2   | B3   | B4   | B5   | B6   | B7
| B8   | B9   | B10  | B11  | B12  | B13  | B14  | B15  | B16  | B17
| B18  | B19  | B20  | B21  | B22  | B23  | B24  | B25  | B26  | B27
| B28  | B29  | B30  | B31  | B32  | B33  | B34  | B35  | B36  | B37
| B38  | B39  | B40  | B41  | B42  | B43  | B44  | B45  | B46  | B47
| B48  | B49  | B50  | B51  | B52  | B53  | B54  | B55  | B56  | B57
| B58  | B59  | B60  | B61  | B62  | B63  | B64  | B65  | B66  | B67
| B68  | B69  | B70  | B71  | B72  | B73  | B74  | B75  | B76  | B77
| B78  | B79  | B80  | B81  | B82  | B83  | B84  | B85  | B86  | B87
| B88  | B89  | B90  | B91  | B92  | B93  | B94  | B95  | B96  | B97
| B98  | B99  | B100 | B101 | B102 | B103 | B104 | B105 | B106 | B107
| B108 | B109 | B110 | B111 | B112 | B113 | B114 | B115 | B116 | B117
| B118 | B119 | B120 | B121 | B122 | B123 | B124 | B125 | B126 | B127
| B128 | B129 | B130 | B131 | B132 | B133 | B134 | B135 | B136 | B137
| B138 | B139 | B140 | B141 | B142 | B143 | B144 | B145 | B146 | B147
| B148 | B149 | B150 | B151 | B152 | B153 | B154 | B155 | B156 | B157
| B158 | B159 | B160 | B161 | B162 | B163 | B164 | B165 | B166 | B167
| B168 | B169 | B170 | B171 | B172 | B173 | B174 | B175 | B176 | B177
| B178 | B179 | B180 | B181 | B182 | B183 | B184 | B185 | B186 | B187
| B188 | B189 | B190 | B191 | B192 | B193 | B194 | B195 | B196 | B197
| B198 | B199 | B200 | B201
.
Definition test_all_reg : list test_reg_t := [
  A    ; B    ; B0   ; B1   ; B2   ; B3   ; B4   ; B5   ; B6   ; B7   ;
  B8   ; B9   ; B10  ; B11  ; B12  ; B13  ; B14  ; B15  ; B16  ; B17  ;
  B18  ; B19  ; B20  ; B21  ; B22  ; B23  ; B24  ; B25  ; B26  ; B27  ;
  B28  ; B29  ; B30  ; B31  ; B32  ; B33  ; B34  ; B35  ; B36  ; B37  ;
  B38  ; B39  ; B40  ; B41  ; B42  ; B43  ; B44  ; B45  ; B46  ; B47  ;
  B48  ; B49  ; B50  ; B51  ; B52  ; B53  ; B54  ; B55  ; B56  ; B57  ;
  B58  ; B59  ; B60  ; B61  ; B62  ; B63  ; B64  ; B65  ; B66  ; B67  ;
  B68  ; B69  ; B70  ; B71  ; B72  ; B73  ; B74  ; B75  ; B76  ; B77  ;
  B78  ; B79  ; B80  ; B81  ; B82  ; B83  ; B84  ; B85  ; B86  ; B87  ;
  B88  ; B89  ; B90  ; B91  ; B92  ; B93  ; B94  ; B95  ; B96  ; B97  ;
  B98  ; B99  ; B100 ; B101 ; B102 ; B103 ; B104 ; B105 ; B106 ; B107 ;
  B108 ; B109 ; B110 ; B111 ; B112 ; B113 ; B114 ; B115 ; B116 ; B117 ;
  B118 ; B119 ; B120 ; B121 ; B122 ; B123 ; B124 ; B125 ; B126 ; B127 ;
  B128 ; B129 ; B130 ; B131 ; B132 ; B133 ; B134 ; B135 ; B136 ; B137 ;
  B138 ; B139 ; B140 ; B141 ; B142 ; B143 ; B144 ; B145 ; B146 ; B147 ;
  B148 ; B149 ; B150 ; B151 ; B152 ; B153 ; B154 ; B155 ; B156 ; B157 ;
  B158 ; B159 ; B160 ; B161 ; B162 ; B163 ; B164 ; B165 ; B166 ; B167 ;
  B168 ; B169 ; B170 ; B171 ; B172 ; B173 ; B174 ; B175 ; B176 ; B177 ;
  B178 ; B179 ; B180 ; B181 ; B182 ; B183 ; B184 ; B185 ; B186 ; B187 ;
  B188 ; B189 ; B190 ; B191 ; B192 ; B193 ; B194 ; B195 ; B196 ; B197 ;
  B198 ; B199 ; B200 ; B201
].
Definition test_get_pos (x : test_reg_t) : nat :=
  match x with
  | A  => 0
  | B  => 5
  | B0 => 8
  | B1 => 11
  | B2 => 14
  | B3 => 17
  | B4 => 20
  | B5 => 23
  | B6 => 26
  | B7 => 29
  | B8 => 32
  | B9 => 35
  | B10 => 38
  | B11 => 41
  | B12 => 44
  | B13 => 47
  | B14 => 50
  | B15 => 53
  | B16 => 56
  | B17 => 59
  | B18 => 62
  | B19 => 65
  | B20 => 68
  | B21 => 71
  | B22 => 74
  | B23 => 77
  | B24 => 80
  | B25 => 83
  | B26 => 86
  | B27 => 89
  | B28 => 92
  | B29 => 95
  | B30 => 98
  | B31 => 101
  | B32 => 104
  | B33 => 107
  | B34 => 110
  | B35 => 113
  | B36 => 116
  | B37 => 119
  | B38 => 122
  | B39 => 125
  | B40 => 128
  | B41 => 131
  | B42 => 134
  | B43 => 137
  | B44 => 140
  | B45 => 143
  | B46 => 146
  | B47 => 149
  | B48 => 152
  | B49 => 155
  | B50 => 158
  | B51 => 161
  | B52 => 164
  | B53 => 167
  | B54 => 170
  | B55 => 173
  | B56 => 176
  | B57 => 179
  | B58 => 182
  | B59 => 185
  | B60 => 188
  | B61 => 191
  | B62 => 194
  | B63 => 197
  | B64 => 200
  | B65 => 203
  | B66 => 206
  | B67 => 209
  | B68 => 212
  | B69 => 215
  | B70 => 218
  | B71 => 221
  | B72 => 224
  | B73 => 227
  | B74 => 230
  | B75 => 233
  | B76 => 236
  | B77 => 239
  | B78 => 242
  | B79 => 245
  | B80 => 248
  | B81 => 251
  | B82 => 254
  | B83 => 257
  | B84 => 260
  | B85 => 263
  | B86 => 266
  | B87 => 269
  | B88 => 272
  | B89 => 275
  | B90 => 278
  | B91 => 281
  | B92 => 284
  | B93 => 287
  | B94 => 290
  | B95 => 293
  | B96 => 296
  | B97 => 299
  | B98 => 302
  | B99 => 305
  | B100 => 308
  | B101 => 311
  | B102 => 314
  | B103 => 317
  | B104 => 320
  | B105 => 323
  | B106 => 326
  | B107 => 329
  | B108 => 332
  | B109 => 335
  | B110 => 338
  | B111 => 341
  | B112 => 344
  | B113 => 347
  | B114 => 350
  | B115 => 353
  | B116 => 356
  | B117 => 359
  | B118 => 362
  | B119 => 365
  | B120 => 368
  | B121 => 371
  | B122 => 374
  | B123 => 377
  | B124 => 380
  | B125 => 383
  | B126 => 386
  | B127 => 389
  | B128 => 392
  | B129 => 395
  | B130 => 398
  | B131 => 401
  | B132 => 404
  | B133 => 407
  | B134 => 410
  | B135 => 413
  | B136 => 416
  | B137 => 419
  | B138 => 422
  | B139 => 425
  | B140 => 428
  | B141 => 431
  | B142 => 434
  | B143 => 437
  | B144 => 440
  | B145 => 443
  | B146 => 446
  | B147 => 449
  | B148 => 452
  | B149 => 455
  | B150 => 458
  | B151 => 461
  | B152 => 464
  | B153 => 467
  | B154 => 470
  | B155 => 473
  | B156 => 476
  | B157 => 479
  | B158 => 482
  | B159 => 485
  | B160 => 488
  | B161 => 491
  | B162 => 494
  | B163 => 497
  | B164 => 500
  | B165 => 503
  | B166 => 506
  | B167 => 509
  | B168 => 512
  | B169 => 515
  | B170 => 518
  | B171 => 521
  | B172 => 524
  | B173 => 527
  | B174 => 530
  | B175 => 533
  | B176 => 536
  | B177 => 539
  | B178 => 542
  | B179 => 545
  | B180 => 548
  | B181 => 551
  | B182 => 554
  | B183 => 557
  | B184 => 560
  | B185 => 563
  | B186 => 566
  | B187 => 569
  | B188 => 572
  | B189 => 575
  | B190 => 578
  | B191 => 581
  | B192 => 584
  | B193 => 587
  | B194 => 590
  | B195 => 593
  | B196 => 596
  | B197 => 599
  | B198 => 602
  | B199 => 605
  | B200 => 608
  | B201 => 611
  end.
Definition test_get_size (x : test_reg_t) : nat :=
  match x with
  | A => 5    | B => 3    | B0 => 3   | B1 => 3   | B2 => 3
  | B3 => 3   | B4 => 3   | B5 => 3   | B6 => 3   | B7 => 3
  | B8 => 3   | B9 => 3   | B10 => 3  | B11 => 3  | B12 => 3
  | B13 => 3  | B14 => 3  | B15 => 3  | B16 => 3  | B17 => 3
  | B18 => 3  | B19 => 3  | B20 => 3  | B21 => 3  | B22 => 3
  | B23 => 3  | B24 => 3  | B25 => 3  | B26 => 3  | B27 => 3
  | B28 => 3  | B29 => 3  | B30 => 3  | B31 => 3  | B32 => 3
  | B33 => 3  | B34 => 3  | B35 => 3  | B36 => 3  | B37 => 3
  | B38 => 3  | B39 => 3  | B40 => 3  | B41 => 3  | B42 => 3
  | B43 => 3  | B44 => 3  | B45 => 3  | B46 => 3  | B47 => 3
  | B48 => 3  | B49 => 3  | B50 => 3  | B51 => 3  | B52 => 3
  | B53 => 3  | B54 => 3  | B55 => 3  | B56 => 3  | B57 => 3
  | B58 => 3  | B59 => 3  | B60 => 3  | B61 => 3  | B62 => 3
  | B63 => 3  | B64 => 3  | B65 => 3  | B66 => 3  | B67 => 3
  | B68 => 3  | B69 => 3  | B70 => 3  | B71 => 3  | B72 => 3
  | B73 => 3  | B74 => 3  | B75 => 3  | B76 => 3  | B77 => 3
  | B78 => 3  | B79 => 3  | B80 => 3  | B81 => 3  | B82 => 3
  | B83 => 3  | B84 => 3  | B85 => 3  | B86 => 3  | B87 => 3
  | B88 => 3  | B89 => 3  | B90 => 3  | B91 => 3  | B92 => 3
  | B93 => 3  | B94 => 3  | B95 => 3  | B96 => 3  | B97 => 3
  | B98 => 3  | B99 => 3  | B100 => 3 | B101 => 3 | B102 => 3
  | B103 => 3 | B104 => 3 | B105 => 3 | B106 => 3 | B107 => 3
  | B108 => 3 | B109 => 3 | B110 => 3 | B111 => 3 | B112 => 3
  | B113 => 3 | B114 => 3 | B115 => 3 | B116 => 3 | B117 => 3
  | B118 => 3 | B119 => 3 | B120 => 3 | B121 => 3 | B122 => 3
  | B123 => 3 | B124 => 3 | B125 => 3 | B126 => 3 | B127 => 3
  | B128 => 3 | B129 => 3 | B130 => 3 | B131 => 3 | B132 => 3
  | B133 => 3 | B134 => 3 | B135 => 3 | B136 => 3 | B137 => 3
  | B138 => 3 | B139 => 3 | B140 => 3 | B141 => 3 | B142 => 3
  | B143 => 3 | B144 => 3 | B145 => 3 | B146 => 3 | B147 => 3
  | B148 => 3 | B149 => 3 | B150 => 3 | B151 => 3 | B152 => 3
  | B153 => 3 | B154 => 3 | B155 => 3 | B156 => 3 | B157 => 3
  | B158 => 3 | B159 => 3 | B160 => 3 | B161 => 3 | B162 => 3
  | B163 => 3 | B164 => 3 | B165 => 3 | B166 => 3 | B167 => 3
  | B168 => 3 | B169 => 3 | B170 => 3 | B171 => 3 | B172 => 3
  | B173 => 3 | B174 => 3 | B175 => 3 | B176 => 3 | B177 => 3
  | B178 => 3 | B179 => 3 | B180 => 3 | B181 => 3 | B182 => 3
  | B183 => 3 | B184 => 3 | B185 => 3 | B186 => 3 | B187 => 3
  | B188 => 3 | B189 => 3 | B190 => 3 | B191 => 3 | B192 => 3
  | B193 => 3 | B194 => 3 | B195 => 3 | B196 => 3 | B197 => 3
  | B198 => 3 | B199 => 3 | B200 => 3 | B201 => 3
  end.
Definition test_get_initial_value (x : test_reg_t) : list bool:=
  match x with
  | A => [false; false; false; true; false]
  | B => [false; true; true]
  | B0 => [false; true; true]
  | B1 => [false; true; true]
  | B2 => [false; true; true]
  | B3 => [false; true; true]
  | B4 => [false; true; true]
  | B5 => [false; true; true]
  | B6 => [false; true; true]
  | B7 => [false; true; true]
  | B8 => [false; true; true]
  | B9 => [false; true; true]
  | B10 => [false; true; true]
  | B11 => [false; true; true]
  | B12 => [false; true; true]
  | B13 => [false; true; true]
  | B14 => [false; true; true]
  | B15 => [false; true; true]
  | B16 => [false; true; true]
  | B17 => [false; true; true]
  | B18 => [false; true; true]
  | B19 => [false; true; true]
  | B20 => [false; true; true]
  | B21 => [false; true; true]
  | B22 => [false; true; true]
  | B23 => [false; true; true]
  | B24 => [false; true; true]
  | B25 => [false; true; true]
  | B26 => [false; true; true]
  | B27 => [false; true; true]
  | B28 => [false; true; true]
  | B29 => [false; true; true]
  | B30 => [false; true; true]
  | B31 => [false; true; true]
  | B32 => [false; true; true]
  | B33 => [false; true; true]
  | B34 => [false; true; true]
  | B35 => [false; true; true]
  | B36 => [false; true; true]
  | B37 => [false; true; true]
  | B38 => [false; true; true]
  | B39 => [false; true; true]
  | B40 => [false; true; true]
  | B41 => [false; true; true]
  | B42 => [false; true; true]
  | B43 => [false; true; true]
  | B44 => [false; true; true]
  | B45 => [false; true; true]
  | B46 => [false; true; true]
  | B47 => [false; true; true]
  | B48 => [false; true; true]
  | B49 => [false; true; true]
  | B50 => [false; true; true]
  | B51 => [false; true; true]
  | B52 => [false; true; true]
  | B53 => [false; true; true]
  | B54 => [false; true; true]
  | B55 => [false; true; true]
  | B56 => [false; true; true]
  | B57 => [false; true; true]
  | B58 => [false; true; true]
  | B59 => [false; true; true]
  | B60 => [false; true; true]
  | B61 => [false; true; true]
  | B62 => [false; true; true]
  | B63 => [false; true; true]
  | B64 => [false; true; true]
  | B65 => [false; true; true]
  | B66 => [false; true; true]
  | B67 => [false; true; true]
  | B68 => [false; true; true]
  | B69 => [false; true; true]
  | B70 => [false; true; true]
  | B71 => [false; true; true]
  | B72 => [false; true; true]
  | B73 => [false; true; true]
  | B74 => [false; true; true]
  | B75 => [false; true; true]
  | B76 => [false; true; true]
  | B77 => [false; true; true]
  | B78 => [false; true; true]
  | B79 => [false; true; true]
  | B80 => [false; true; true]
  | B81 => [false; true; true]
  | B82 => [false; true; true]
  | B83 => [false; true; true]
  | B84 => [false; true; true]
  | B85 => [false; true; true]
  | B86 => [false; true; true]
  | B87 => [false; true; true]
  | B88 => [false; true; true]
  | B89 => [false; true; true]
  | B90 => [false; true; true]
  | B91 => [false; true; true]
  | B92 => [false; true; true]
  | B93 => [false; true; true]
  | B94 => [false; true; true]
  | B95 => [false; true; true]
  | B96 => [false; true; true]
  | B97 => [false; true; true]
  | B98 => [false; true; true]
  | B99 => [false; true; true]
  | B100 => [false; true; true]
  | B101 => [false; true; true]
  | B102 => [false; true; true]
  | B103 => [false; true; true]
  | B104 => [false; true; true]
  | B105 => [false; true; true]
  | B106 => [false; true; true]
  | B107 => [false; true; true]
  | B108 => [false; true; true]
  | B109 => [false; true; true]
  | B110 => [false; true; true]
  | B111 => [false; true; true]
  | B112 => [false; true; true]
  | B113 => [false; true; true]
  | B114 => [false; true; true]
  | B115 => [false; true; true]
  | B116 => [false; true; true]
  | B117 => [false; true; true]
  | B118 => [false; true; true]
  | B119 => [false; true; true]
  | B120 => [false; true; true]
  | B121 => [false; true; true]
  | B122 => [false; true; true]
  | B123 => [false; true; true]
  | B124 => [false; true; true]
  | B125 => [false; true; true]
  | B126 => [false; true; true]
  | B127 => [false; true; true]
  | B128 => [false; true; true]
  | B129 => [false; true; true]
  | B130 => [false; true; true]
  | B131 => [false; true; true]
  | B132 => [false; true; true]
  | B133 => [false; true; true]
  | B134 => [false; true; true]
  | B135 => [false; true; true]
  | B136 => [false; true; true]
  | B137 => [false; true; true]
  | B138 => [false; true; true]
  | B139 => [false; true; true]
  | B140 => [false; true; true]
  | B141 => [false; true; true]
  | B142 => [false; true; true]
  | B143 => [false; true; true]
  | B144 => [false; true; true]
  | B145 => [false; true; true]
  | B146 => [false; true; true]
  | B147 => [false; true; true]
  | B148 => [false; true; true]
  | B149 => [false; true; true]
  | B150 => [false; true; true]
  | B151 => [false; true; true]
  | B152 => [false; true; true]
  | B153 => [false; true; true]
  | B154 => [false; true; true]
  | B155 => [false; true; true]
  | B156 => [false; true; true]
  | B157 => [false; true; true]
  | B158 => [false; true; true]
  | B159 => [false; true; true]
  | B160 => [false; true; true]
  | B161 => [false; true; true]
  | B162 => [false; true; true]
  | B163 => [false; true; true]
  | B164 => [false; true; true]
  | B165 => [false; true; true]
  | B166 => [false; true; true]
  | B167 => [false; true; true]
  | B168 => [false; true; true]
  | B169 => [false; true; true]
  | B170 => [false; true; true]
  | B171 => [false; true; true]
  | B172 => [false; true; true]
  | B173 => [false; true; true]
  | B174 => [false; true; true]
  | B175 => [false; true; true]
  | B176 => [false; true; true]
  | B177 => [false; true; true]
  | B178 => [false; true; true]
  | B179 => [false; true; true]
  | B180 => [false; true; true]
  | B181 => [false; true; true]
  | B182 => [false; true; true]
  | B183 => [false; true; true]
  | B184 => [false; true; true]
  | B185 => [false; true; true]
  | B186 => [false; true; true]
  | B187 => [false; true; true]
  | B188 => [false; true; true]
  | B189 => [false; true; true]
  | B190 => [false; true; true]
  | B191 => [false; true; true]
  | B192 => [false; true; true]
  | B193 => [false; true; true]
  | B194 => [false; true; true]
  | B195 => [false; true; true]
  | B196 => [false; true; true]
  | B197 => [false; true; true]
  | B198 => [false; true; true]
  | B199 => [false; true; true]
  | B200 => [false; true; true]
  | B201 => [false; true; true]
  end.

Definition test_initial_map :=
  @initial_map test_reg_t test_all_reg test_get_initial_value.
Compute @map_get test_reg_t test_get_pos test_get_size test_initial_map B200.
Compute @map_set test_reg_t test_get_pos test_get_size test_initial_map B200 [true; true; true].

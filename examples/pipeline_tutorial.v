(*! Tutorial: Simple arithmetic pipeline !*)
Require Import Koika.Frontend.

(*|
===========================================================
 A simple arithmetic pipeline and its proof of correctness
===========================================================

In this file we model a simple arithmetic pipeline with two functions `f` and `g`::

  input ---(f)--> queue ---(g)--> output

For simplicity, ``input`` and ``output`` will be registers, and we'll update ``input`` at the end of each cycle using an external function ``next_input`` (think of it as an oracle).

Our system will have two rules: ``doF`` and ``doG``, each corresponding to one step of the pipeline.

All that follows is parameterized on a register size ``sz``, set to 32 bits by default.
|*)

Definition sz := 32.

(*|
Setup
=====

We start by defining the system using inductive types to declare its registers and rules and their types:
|*)

Inductive reg_t :=
| input_buffer (** The data source (from which we read inputs) *)
| queue_empty (** A flag indicating whether the queue is empty *)
| queue_data (** The data stored in the queue *)
| output_buffer (** The data sink (into which we write outputs) *)
| output_buffer_1 (** The data sink (into which we write outputs) *)
| output_buffer_2 (** The data sink (into which we write outputs) *)
| output_buffer_3 (** The data sink (into which we write outputs) *)
| output_buffer_4 (** The data sink (into which we write outputs) *)
| output_buffer_5 (** The data sink (into which we write outputs) *)
| output_buffer_6 (** The data sink (into which we write outputs) *)
| output_buffer_7 (** The data sink (into which we write outputs) *)
| output_buffer_8 (** The data sink (into which we write outputs) *)
| output_buffer_9 (** The data sink (into which we write outputs) *)
| output_buffer_10 (** The data sink (into which we write outputs) *)
| output_buffer_11 (** The data sink (into which we write outputs) *)
| output_buffer_12 (** The data sink (into which we write outputs) *)
| output_buffer_13 (** The data sink (into which we write outputs) *)
| output_buffer_14 (** The data sink (into which we write outputs) *)
| output_buffer_15 (** The data sink (into which we write outputs) *)
| output_buffer_16 (** The data sink (into which we write outputs) *)
| output_buffer_17 (** The data sink (into which we write outputs) *)
| output_buffer_18 (** The data sink (into which we write outputs) *)
| output_buffer_19 (** The data sink (into which we write outputs) *)
| output_buffer_20 (** The data sink (into which we write outputs) *)
| output_buffer_21 (** The data sink (into which we write outputs) *)
| output_buffer_22 (** The data sink (into which we write outputs) *)
| output_buffer_23 (** The data sink (into which we write outputs) *)
| output_buffer_24 (** The data sink (into which we write outputs) *)
| output_buffer_25 (** The data sink (into which we write outputs) *)
| output_buffer_26 (** The data sink (into which we write outputs) *)
| output_buffer_27 (** The data sink (into which we write outputs) *)
| output_buffer_28 (** The data sink (into which we write outputs) *)
| output_buffer_29 (** The data sink (into which we write outputs) *)
| output_buffer_30 (** The data sink (into which we write outputs) *)
| output_buffer_31 (** The data sink (into which we write outputs) *)
| output_buffer_32 (** The data sink (into which we write outputs) *)
| output_buffer_33 (** The data sink (into which we write outputs) *)
| output_buffer_34 (** The data sink (into which we write outputs) *)
| output_buffer_35 (** The data sink (into which we write outputs) *)
| output_buffer_36 (** The data sink (into which we write outputs) *)
| output_buffer_37 (** The data sink (into which we write outputs) *)
| output_buffer_38 (** The data sink (into which we write outputs) *)
| output_buffer_39 (** The data sink (into which we write outputs) *)
| output_buffer_40 (** The data sink (into which we write outputs) *)
| output_buffer_41 (** The data sink (into which we write outputs) *)
| output_buffer_42 (** The data sink (into which we write outputs) *)
| output_buffer_43 (** The data sink (into which we write outputs) *)
| output_buffer_44 (** The data sink (into which we write outputs) *)
| output_buffer_45 (** The data sink (into which we write outputs) *)
| output_buffer_46 (** The data sink (into which we write outputs) *)
| output_buffer_47 (** The data sink (into which we write outputs) *)
| output_buffer_48 (** The data sink (into which we write outputs) *)
| output_buffer_49 (** The data sink (into which we write outputs) *)
| output_buffer_50 (** The data sink (into which we write outputs) *)
| output_buffer_51 (** The data sink (into which we write outputs) *)
| output_buffer_52 (** The data sink (into which we write outputs) *)
| output_buffer_53 (** The data sink (into which we write outputs) *)
| output_buffer_54 (** The data sink (into which we write outputs) *)
| output_buffer_55 (** The data sink (into which we write outputs) *)
| output_buffer_56 (** The data sink (into which we write outputs) *)
| output_buffer_57 (** The data sink (into which we write outputs) *)
| output_buffer_58 (** The data sink (into which we write outputs) *)
| output_buffer_59 (** The data sink (into which we write outputs) *)
| output_buffer_60 (** The data sink (into which we write outputs) *)
| output_buffer_61 (** The data sink (into which we write outputs) *)
| output_buffer_62 (** The data sink (into which we write outputs) *)
| output_buffer_63 (** The data sink (into which we write outputs) *)
| output_buffer_64 (** The data sink (into which we write outputs) *)
| output_buffer_65 (** The data sink (into which we write outputs) *)
| output_buffer_66 (** The data sink (into which we write outputs) *)
| output_buffer_67 (** The data sink (into which we write outputs) *)
| output_buffer_68 (** The data sink (into which we write outputs) *)
| output_buffer_69 (** The data sink (into which we write outputs) *)
| output_buffer_70 (** The data sink (into which we write outputs) *)
| output_buffer_71 (** The data sink (into which we write outputs) *)
| output_buffer_72 (** The data sink (into which we write outputs) *)
| output_buffer_73 (** The data sink (into which we write outputs) *)
| output_buffer_74 (** The data sink (into which we write outputs) *)
| output_buffer_75 (** The data sink (into which we write outputs) *)
| output_buffer_76 (** The data sink (into which we write outputs) *)
| output_buffer_77 (** The data sink (into which we write outputs) *)
| output_buffer_78 (** The data sink (into which we write outputs) *)
| output_buffer_79 (** The data sink (into which we write outputs) *)
| output_buffer_80 (** The data sink (into which we write outputs) *)
| output_buffer_81 (** The data sink (into which we write outputs) *)
| output_buffer_82 (** The data sink (into which we write outputs) *)
| output_buffer_83 (** The data sink (into which we write outputs) *)
| output_buffer_84 (** The data sink (into which we write outputs) *)
| output_buffer_85 (** The data sink (into which we write outputs) *)
| output_buffer_86 (** The data sink (into which we write outputs) *)
| output_buffer_87 (** The data sink (into which we write outputs) *)
| output_buffer_88 (** The data sink (into which we write outputs) *)
| output_buffer_89 (** The data sink (into which we write outputs) *)
| output_buffer_90 (** The data sink (into which we write outputs) *)
| output_buffer_91 (** The data sink (into which we write outputs) *)
| output_buffer_92 (** The data sink (into which we write outputs) *)
| output_buffer_93 (** The data sink (into which we write outputs) *)
| output_buffer_94 (** The data sink (into which we write outputs) *)
| output_buffer_95 (** The data sink (into which we write outputs) *)
| output_buffer_96 (** The data sink (into which we write outputs) *)
| output_buffer_97 (** The data sink (into which we write outputs) *)
| output_buffer_98 (** The data sink (into which we write outputs) *)
| output_buffer_99 (** The data sink (into which we write outputs) *)
| output_buffer_100 (** The data sink (into which we write outputs) *)
| output_buffer_101 (** The data sink (into which we write outputs) *)
| output_buffer_102 (** The data sink (into which we write outputs) *)
| output_buffer_103 (** The data sink (into which we write outputs) *)
| output_buffer_104 (** The data sink (into which we write outputs) *)
| output_buffer_105 (** The data sink (into which we write outputs) *)
| output_buffer_106 (** The data sink (into which we write outputs) *)
| output_buffer_107 (** The data sink (into which we write outputs) *)
| output_buffer_108 (** The data sink (into which we write outputs) *)
| output_buffer_109 (** The data sink (into which we write outputs) *)
| output_buffer_110 (** The data sink (into which we write outputs) *)
| output_buffer_111 (** The data sink (into which we write outputs) *)
| output_buffer_112 (** The data sink (into which we write outputs) *)
| output_buffer_113 (** The data sink (into which we write outputs) *)
| output_buffer_114 (** The data sink (into which we write outputs) *)
| output_buffer_115 (** The data sink (into which we write outputs) *)
| output_buffer_116 (** The data sink (into which we write outputs) *)
| output_buffer_117 (** The data sink (into which we write outputs) *)
| output_buffer_118 (** The data sink (into which we write outputs) *)
| output_buffer_119 (** The data sink (into which we write outputs) *)
| output_buffer_120 (** The data sink (into which we write outputs) *)
| output_buffer_121 (** The data sink (into which we write outputs) *)
| output_buffer_122 (** The data sink (into which we write outputs) *)
| output_buffer_123 (** The data sink (into which we write outputs) *)
| output_buffer_124 (** The data sink (into which we write outputs) *)
| output_buffer_125 (** The data sink (into which we write outputs) *)
| output_buffer_126 (** The data sink (into which we write outputs) *)
| output_buffer_127 (** The data sink (into which we write outputs) *)
| output_buffer_128 (** The data sink (into which we write outputs) *)
| output_buffer_129 (** The data sink (into which we write outputs) *)
| output_buffer_130 (** The data sink (into which we write outputs) *)
| output_buffer_131 (** The data sink (into which we write outputs) *)
| output_buffer_132 (** The data sink (into which we write outputs) *)
| output_buffer_133 (** The data sink (into which we write outputs) *)
| output_buffer_134 (** The data sink (into which we write outputs) *)
| output_buffer_135 (** The data sink (into which we write outputs) *)
| output_buffer_136 (** The data sink (into which we write outputs) *)
| output_buffer_137 (** The data sink (into which we write outputs) *)
| output_buffer_138 (** The data sink (into which we write outputs) *)
| output_buffer_139 (** The data sink (into which we write outputs) *)
| output_buffer_140 (** The data sink (into which we write outputs) *)
| output_buffer_141 (** The data sink (into which we write outputs) *)
| output_buffer_142 (** The data sink (into which we write outputs) *)
| output_buffer_143 (** The data sink (into which we write outputs) *)
| output_buffer_144 (** The data sink (into which we write outputs) *)
| output_buffer_145 (** The data sink (into which we write outputs) *)
| output_buffer_146 (** The data sink (into which we write outputs) *)
| output_buffer_147 (** The data sink (into which we write outputs) *)
| output_buffer_148 (** The data sink (into which we write outputs) *)
| output_buffer_149 (** The data sink (into which we write outputs) *)
| output_buffer_150 (** The data sink (into which we write outputs) *)
| output_buffer_151 (** The data sink (into which we write outputs) *)
| output_buffer_152 (** The data sink (into which we write outputs) *)
| output_buffer_153 (** The data sink (into which we write outputs) *)
| output_buffer_154 (** The data sink (into which we write outputs) *)
| output_buffer_155 (** The data sink (into which we write outputs) *)
| output_buffer_156 (** The data sink (into which we write outputs) *)
| output_buffer_157 (** The data sink (into which we write outputs) *)
| output_buffer_158 (** The data sink (into which we write outputs) *)
| output_buffer_159 (** The data sink (into which we write outputs) *)
| output_buffer_160 (** The data sink (into which we write outputs) *)
| output_buffer_161 (** The data sink (into which we write outputs) *)
| output_buffer_162 (** The data sink (into which we write outputs) *)
| output_buffer_163 (** The data sink (into which we write outputs) *)
| output_buffer_164 (** The data sink (into which we write outputs) *)
| output_buffer_165 (** The data sink (into which we write outputs) *)
| output_buffer_166 (** The data sink (into which we write outputs) *)
| output_buffer_167 (** The data sink (into which we write outputs) *)
| output_buffer_168 (** The data sink (into which we write outputs) *)
| output_buffer_169 (** The data sink (into which we write outputs) *)
| output_buffer_170 (** The data sink (into which we write outputs) *)
| output_buffer_171 (** The data sink (into which we write outputs) *)
| output_buffer_172 (** The data sink (into which we write outputs) *)
| output_buffer_173 (** The data sink (into which we write outputs) *)
| output_buffer_174 (** The data sink (into which we write outputs) *)
| output_buffer_175 (** The data sink (into which we write outputs) *)
| output_buffer_176 (** The data sink (into which we write outputs) *)
| output_buffer_177 (** The data sink (into which we write outputs) *)
| output_buffer_178 (** The data sink (into which we write outputs) *)
| output_buffer_179 (** The data sink (into which we write outputs) *)
| output_buffer_180 (** The data sink (into which we write outputs) *)
| output_buffer_181 (** The data sink (into which we write outputs) *)
| output_buffer_182 (** The data sink (into which we write outputs) *)
| output_buffer_183 (** The data sink (into which we write outputs) *)
| output_buffer_184 (** The data sink (into which we write outputs) *)
| output_buffer_185 (** The data sink (into which we write outputs) *)
| output_buffer_186 (** The data sink (into which we write outputs) *)
| output_buffer_187 (** The data sink (into which we write outputs) *)
| output_buffer_188 (** The data sink (into which we write outputs) *)
| output_buffer_189 (** The data sink (into which we write outputs) *)
| output_buffer_190 (** The data sink (into which we write outputs) *)
| output_buffer_191 (** The data sink (into which we write outputs) *)
| output_buffer_192 (** The data sink (into which we write outputs) *)
| output_buffer_193 (** The data sink (into which we write outputs) *)
| output_buffer_194 (** The data sink (into which we write outputs) *)
| output_buffer_195 (** The data sink (into which we write outputs) *)
| output_buffer_196 (** The data sink (into which we write outputs) *)
| output_buffer_197 (** The data sink (into which we write outputs) *)
| output_buffer_198 (** The data sink (into which we write outputs) *)
| output_buffer_199 (** The data sink (into which we write outputs) *)
| output_buffer_200 (** The data sink (into which we write outputs) *)
| output_buffer_201 (** The data sink (into which we write outputs) *)
| output_buffer_202 (** The data sink (into which we write outputs) *)
| output_buffer_203 (** The data sink (into which we write outputs) *)
| output_buffer_204 (** The data sink (into which we write outputs) *)
| output_buffer_205 (** The data sink (into which we write outputs) *)
| output_buffer_206 (** The data sink (into which we write outputs) *)
| output_buffer_207 (** The data sink (into which we write outputs) *)
| output_buffer_208 (** The data sink (into which we write outputs) *)
| output_buffer_209 (** The data sink (into which we write outputs) *)
| output_buffer_210 (** The data sink (into which we write outputs) *)
| output_buffer_211 (** The data sink (into which we write outputs) *)
| output_buffer_212 (** The data sink (into which we write outputs) *)
| output_buffer_213 (** The data sink (into which we write outputs) *)
| output_buffer_214 (** The data sink (into which we write outputs) *)
| output_buffer_215 (** The data sink (into which we write outputs) *)
| output_buffer_216 (** The data sink (into which we write outputs) *)
| output_buffer_217 (** The data sink (into which we write outputs) *)
| output_buffer_218 (** The data sink (into which we write outputs) *)
| output_buffer_219 (** The data sink (into which we write outputs) *)
| output_buffer_220 (** The data sink (into which we write outputs) *)
| output_buffer_221 (** The data sink (into which we write outputs) *)
| output_buffer_222 (** The data sink (into which we write outputs) *)
| output_buffer_223 (** The data sink (into which we write outputs) *)
| output_buffer_224 (** The data sink (into which we write outputs) *)
| output_buffer_225 (** The data sink (into which we write outputs) *)
| output_buffer_226 (** The data sink (into which we write outputs) *)
| output_buffer_227 (** The data sink (into which we write outputs) *)
| output_buffer_228 (** The data sink (into which we write outputs) *)
| output_buffer_229 (** The data sink (into which we write outputs) *)
| output_buffer_230 (** The data sink (into which we write outputs) *)
| output_buffer_231 (** The data sink (into which we write outputs) *)
| output_buffer_232 (** The data sink (into which we write outputs) *)
| output_buffer_233 (** The data sink (into which we write outputs) *)
| output_buffer_234 (** The data sink (into which we write outputs) *)
| output_buffer_235 (** The data sink (into which we write outputs) *)
| output_buffer_236 (** The data sink (into which we write outputs) *)
| output_buffer_237 (** The data sink (into which we write outputs) *)
| output_buffer_238 (** The data sink (into which we write outputs) *)
| output_buffer_239 (** The data sink (into which we write outputs) *)
| output_buffer_240 (** The data sink (into which we write outputs) *)
| output_buffer_241 (** The data sink (into which we write outputs) *)
| output_buffer_242 (** The data sink (into which we write outputs) *)
| output_buffer_243 (** The data sink (into which we write outputs) *)
| output_buffer_244 (** The data sink (into which we write outputs) *)
| output_buffer_245 (** The data sink (into which we write outputs) *)
| output_buffer_246 (** The data sink (into which we write outputs) *)
| output_buffer_247 (** The data sink (into which we write outputs) *)
| output_buffer_248 (** The data sink (into which we write outputs) *)
| output_buffer_249 (** The data sink (into which we write outputs) *)
| output_buffer_250 (** The data sink (into which we write outputs) *)
| output_buffer_251 (** The data sink (into which we write outputs) *)
| output_buffer_252 (** The data sink (into which we write outputs) *)
| output_buffer_253 (** The data sink (into which we write outputs) *)
| output_buffer_254 (** The data sink (into which we write outputs) *)
| output_buffer_255 (** The data sink (into which we write outputs) *)
| output_buffer_256 (** The data sink (into which we write outputs) *)
| output_buffer_257 (** The data sink (into which we write outputs) *)
| output_buffer_258 (** The data sink (into which we write outputs) *)
| output_buffer_259 (** The data sink (into which we write outputs) *)
| output_buffer_260 (** The data sink (into which we write outputs) *)
| output_buffer_261 (** The data sink (into which we write outputs) *)
| output_buffer_262 (** The data sink (into which we write outputs) *)
| output_buffer_263 (** The data sink (into which we write outputs) *)
| output_buffer_264 (** The data sink (into which we write outputs) *)
| output_buffer_265 (** The data sink (into which we write outputs) *)
| output_buffer_266 (** The data sink (into which we write outputs) *)
| output_buffer_267 (** The data sink (into which we write outputs) *)
| output_buffer_268 (** The data sink (into which we write outputs) *)
| output_buffer_269 (** The data sink (into which we write outputs) *)
| output_buffer_270 (** The data sink (into which we write outputs) *)
| output_buffer_271 (** The data sink (into which we write outputs) *)
| output_buffer_272 (** The data sink (into which we write outputs) *)
| output_buffer_273 (** The data sink (into which we write outputs) *)
| output_buffer_274 (** The data sink (into which we write outputs) *)
| output_buffer_275 (** The data sink (into which we write outputs) *)
| output_buffer_276 (** The data sink (into which we write outputs) *)
| output_buffer_277 (** The data sink (into which we write outputs) *)
| output_buffer_278 (** The data sink (into which we write outputs) *)
| output_buffer_279 (** The data sink (into which we write outputs) *)
| output_buffer_280 (** The data sink (into which we write outputs) *)
| output_buffer_281 (** The data sink (into which we write outputs) *)
| output_buffer_282 (** The data sink (into which we write outputs) *)
| output_buffer_283 (** The data sink (into which we write outputs) *)
| output_buffer_284 (** The data sink (into which we write outputs) *)
| output_buffer_285 (** The data sink (into which we write outputs) *)
| output_buffer_286 (** The data sink (into which we write outputs) *)
| output_buffer_287 (** The data sink (into which we write outputs) *)
| output_buffer_288 (** The data sink (into which we write outputs) *)
| output_buffer_289 (** The data sink (into which we write outputs) *)
| output_buffer_290 (** The data sink (into which we write outputs) *)
| output_buffer_291 (** The data sink (into which we write outputs) *)
| output_buffer_292 (** The data sink (into which we write outputs) *)
| output_buffer_293 (** The data sink (into which we write outputs) *)
| output_buffer_294 (** The data sink (into which we write outputs) *)
| output_buffer_295 (** The data sink (into which we write outputs) *)
| output_buffer_296 (** The data sink (into which we write outputs) *)
| output_buffer_297 (** The data sink (into which we write outputs) *)
| output_buffer_298 (** The data sink (into which we write outputs) *)
| output_buffer_299 (** The data sink (into which we write outputs) *)
| output_buffer_300 (** The data sink (into which we write outputs) *)
| output_buffer_301 (** The data sink (into which we write outputs) *)
| output_buffer_302 (** The data sink (into which we write outputs) *)
| output_buffer_303 (** The data sink (into which we write outputs) *)
| output_buffer_304 (** The data sink (into which we write outputs) *)
| output_buffer_305 (** The data sink (into which we write outputs) *)
| output_buffer_306 (** The data sink (into which we write outputs) *)
| output_buffer_307 (** The data sink (into which we write outputs) *)
| output_buffer_308 (** The data sink (into which we write outputs) *)
| output_buffer_309 (** The data sink (into which we write outputs) *)
| output_buffer_310 (** The data sink (into which we write outputs) *)
| output_buffer_311 (** The data sink (into which we write outputs) *)
| output_buffer_312 (** The data sink (into which we write outputs) *)
| output_buffer_313 (** The data sink (into which we write outputs) *)
| output_buffer_314 (** The data sink (into which we write outputs) *)
| output_buffer_315 (** The data sink (into which we write outputs) *)
| output_buffer_316 (** The data sink (into which we write outputs) *)
| output_buffer_317 (** The data sink (into which we write outputs) *)
| output_buffer_318 (** The data sink (into which we write outputs) *)
| output_buffer_319 (** The data sink (into which we write outputs) *)
| output_buffer_320 (** The data sink (into which we write outputs) *)
| output_buffer_321 (** The data sink (into which we write outputs) *)
| output_buffer_322 (** The data sink (into which we write outputs) *)
| output_buffer_323 (** The data sink (into which we write outputs) *)
| output_buffer_324 (** The data sink (into which we write outputs) *)
| output_buffer_325 (** The data sink (into which we write outputs) *)
| output_buffer_326 (** The data sink (into which we write outputs) *)
| output_buffer_327 (** The data sink (into which we write outputs) *)
| output_buffer_328 (** The data sink (into which we write outputs) *)
| output_buffer_329 (** The data sink (into which we write outputs) *)
| output_buffer_330 (** The data sink (into which we write outputs) *)
| output_buffer_331 (** The data sink (into which we write outputs) *)
| output_buffer_332 (** The data sink (into which we write outputs) *)
| output_buffer_333 (** The data sink (into which we write outputs) *)
| output_buffer_334 (** The data sink (into which we write outputs) *)
| output_buffer_335 (** The data sink (into which we write outputs) *)
| output_buffer_336 (** The data sink (into which we write outputs) *)
| output_buffer_337 (** The data sink (into which we write outputs) *)
| output_buffer_338 (** The data sink (into which we write outputs) *)
| output_buffer_339 (** The data sink (into which we write outputs) *)
| output_buffer_340 (** The data sink (into which we write outputs) *)
| output_buffer_341 (** The data sink (into which we write outputs) *)
| output_buffer_342 (** The data sink (into which we write outputs) *)
| output_buffer_343 (** The data sink (into which we write outputs) *)
| output_buffer_344 (** The data sink (into which we write outputs) *)
| output_buffer_345 (** The data sink (into which we write outputs) *)
| output_buffer_346 (** The data sink (into which we write outputs) *)
| output_buffer_347 (** The data sink (into which we write outputs) *)
| output_buffer_348 (** The data sink (into which we write outputs) *)
| output_buffer_349 (** The data sink (into which we write outputs) *)
| output_buffer_350 (** The data sink (into which we write outputs) *)
| output_buffer_351 (** The data sink (into which we write outputs) *)
| output_buffer_352 (** The data sink (into which we write outputs) *)
| output_buffer_353 (** The data sink (into which we write outputs) *)
| output_buffer_354 (** The data sink (into which we write outputs) *)
| output_buffer_355 (** The data sink (into which we write outputs) *)
| output_buffer_356 (** The data sink (into which we write outputs) *)
| output_buffer_357 (** The data sink (into which we write outputs) *)
| output_buffer_358 (** The data sink (into which we write outputs) *)
| output_buffer_359 (** The data sink (into which we write outputs) *)
| output_buffer_360 (** The data sink (into which we write outputs) *)
| output_buffer_361 (** The data sink (into which we write outputs) *)
| output_buffer_362 (** The data sink (into which we write outputs) *)
| output_buffer_363 (** The data sink (into which we write outputs) *)
| output_buffer_364 (** The data sink (into which we write outputs) *)
| output_buffer_365 (** The data sink (into which we write outputs) *)
| output_buffer_366 (** The data sink (into which we write outputs) *)
| output_buffer_367 (** The data sink (into which we write outputs) *)
| output_buffer_368 (** The data sink (into which we write outputs) *)
| output_buffer_369 (** The data sink (into which we write outputs) *)
| output_buffer_370 (** The data sink (into which we write outputs) *)
| output_buffer_371 (** The data sink (into which we write outputs) *)
| output_buffer_372 (** The data sink (into which we write outputs) *)
| output_buffer_373 (** The data sink (into which we write outputs) *)
| output_buffer_374 (** The data sink (into which we write outputs) *)
| output_buffer_375 (** The data sink (into which we write outputs) *)
| output_buffer_376 (** The data sink (into which we write outputs) *)
| output_buffer_377 (** The data sink (into which we write outputs) *)
| output_buffer_378 (** The data sink (into which we write outputs) *)
| output_buffer_379 (** The data sink (into which we write outputs) *)
| output_buffer_380 (** The data sink (into which we write outputs) *)
| output_buffer_381 (** The data sink (into which we write outputs) *)
| output_buffer_382 (** The data sink (into which we write outputs) *)
| output_buffer_383 (** The data sink (into which we write outputs) *)
| output_buffer_384 (** The data sink (into which we write outputs) *)
| output_buffer_385 (** The data sink (into which we write outputs) *)
| output_buffer_386 (** The data sink (into which we write outputs) *)
| output_buffer_387 (** The data sink (into which we write outputs) *)
| output_buffer_388 (** The data sink (into which we write outputs) *)
| output_buffer_389 (** The data sink (into which we write outputs) *)
| output_buffer_390 (** The data sink (into which we write outputs) *)
| output_buffer_391 (** The data sink (into which we write outputs) *)
| output_buffer_392 (** The data sink (into which we write outputs) *)
| output_buffer_393 (** The data sink (into which we write outputs) *)
| output_buffer_394 (** The data sink (into which we write outputs) *)
| output_buffer_395 (** The data sink (into which we write outputs) *)
| output_buffer_396 (** The data sink (into which we write outputs) *)
| output_buffer_397 (** The data sink (into which we write outputs) *)
| output_buffer_398 (** The data sink (into which we write outputs) *)
| output_buffer_399 (** The data sink (into which we write outputs) *)
| output_buffer_400 (** The data sink (into which we write outputs) *)
| output_buffer_401 (** The data sink (into which we write outputs) *)
| output_buffer_402 (** The data sink (into which we write outputs) *)
| output_buffer_403 (** The data sink (into which we write outputs) *)
| output_buffer_404 (** The data sink (into which we write outputs) *)
| output_buffer_405 (** The data sink (into which we write outputs) *)
| output_buffer_406 (** The data sink (into which we write outputs) *)
| output_buffer_407 (** The data sink (into which we write outputs) *)
| output_buffer_408 (** The data sink (into which we write outputs) *)
| output_buffer_409 (** The data sink (into which we write outputs) *)
| output_buffer_410 (** The data sink (into which we write outputs) *)
| output_buffer_411 (** The data sink (into which we write outputs) *)
| output_buffer_412 (** The data sink (into which we write outputs) *)
| output_buffer_413 (** The data sink (into which we write outputs) *)
| output_buffer_414 (** The data sink (into which we write outputs) *)
| output_buffer_415 (** The data sink (into which we write outputs) *)
| output_buffer_416 (** The data sink (into which we write outputs) *)
| output_buffer_417 (** The data sink (into which we write outputs) *)
| output_buffer_418 (** The data sink (into which we write outputs) *)
| output_buffer_419 (** The data sink (into which we write outputs) *)
| output_buffer_420 (** The data sink (into which we write outputs) *)
| output_buffer_421 (** The data sink (into which we write outputs) *)
| output_buffer_422 (** The data sink (into which we write outputs) *)
| output_buffer_423 (** The data sink (into which we write outputs) *)
| output_buffer_424 (** The data sink (into which we write outputs) *)
| output_buffer_425 (** The data sink (into which we write outputs) *)
| output_buffer_426 (** The data sink (into which we write outputs) *)
| output_buffer_427 (** The data sink (into which we write outputs) *)
| output_buffer_428 (** The data sink (into which we write outputs) *)
| output_buffer_429 (** The data sink (into which we write outputs) *)
| output_buffer_430 (** The data sink (into which we write outputs) *)
| output_buffer_431 (** The data sink (into which we write outputs) *)
| output_buffer_432 (** The data sink (into which we write outputs) *)
| output_buffer_433 (** The data sink (into which we write outputs) *)
| output_buffer_434 (** The data sink (into which we write outputs) *)
| output_buffer_435 (** The data sink (into which we write outputs) *)
| output_buffer_436 (** The data sink (into which we write outputs) *)
| output_buffer_437 (** The data sink (into which we write outputs) *)
| output_buffer_438 (** The data sink (into which we write outputs) *)
| output_buffer_439 (** The data sink (into which we write outputs) *)
| output_buffer_440 (** The data sink (into which we write outputs) *)
| output_buffer_441 (** The data sink (into which we write outputs) *)
| output_buffer_442 (** The data sink (into which we write outputs) *)
| output_buffer_443 (** The data sink (into which we write outputs) *)
| output_buffer_444 (** The data sink (into which we write outputs) *)
| output_buffer_445 (** The data sink (into which we write outputs) *)
| output_buffer_446 (** The data sink (into which we write outputs) *)
| output_buffer_447 (** The data sink (into which we write outputs) *)
| output_buffer_448 (** The data sink (into which we write outputs) *)
| output_buffer_449 (** The data sink (into which we write outputs) *)
| output_buffer_450 (** The data sink (into which we write outputs) *)
| output_buffer_451 (** The data sink (into which we write outputs) *)
| output_buffer_452 (** The data sink (into which we write outputs) *)
| output_buffer_453 (** The data sink (into which we write outputs) *)
| output_buffer_454 (** The data sink (into which we write outputs) *)
| output_buffer_455 (** The data sink (into which we write outputs) *)
| output_buffer_456 (** The data sink (into which we write outputs) *)
| output_buffer_457 (** The data sink (into which we write outputs) *)
| output_buffer_458 (** The data sink (into which we write outputs) *)
| output_buffer_459 (** The data sink (into which we write outputs) *)
| output_buffer_460 (** The data sink (into which we write outputs) *)
| output_buffer_461 (** The data sink (into which we write outputs) *)
| output_buffer_462 (** The data sink (into which we write outputs) *)
| output_buffer_463 (** The data sink (into which we write outputs) *)
| output_buffer_464 (** The data sink (into which we write outputs) *)
| output_buffer_465 (** The data sink (into which we write outputs) *)
| output_buffer_466 (** The data sink (into which we write outputs) *)
| output_buffer_467 (** The data sink (into which we write outputs) *)
| output_buffer_468 (** The data sink (into which we write outputs) *)
| output_buffer_469 (** The data sink (into which we write outputs) *)
| output_buffer_470 (** The data sink (into which we write outputs) *)
| output_buffer_471 (** The data sink (into which we write outputs) *)
| output_buffer_472 (** The data sink (into which we write outputs) *)
| output_buffer_473 (** The data sink (into which we write outputs) *)
| output_buffer_474 (** The data sink (into which we write outputs) *)
| output_buffer_475 (** The data sink (into which we write outputs) *)
| output_buffer_476 (** The data sink (into which we write outputs) *)
| output_buffer_477 (** The data sink (into which we write outputs) *)
| output_buffer_478 (** The data sink (into which we write outputs) *)
| output_buffer_479 (** The data sink (into which we write outputs) *)
| output_buffer_480 (** The data sink (into which we write outputs) *)
| output_buffer_481 (** The data sink (into which we write outputs) *)
| output_buffer_482 (** The data sink (into which we write outputs) *)
| output_buffer_483 (** The data sink (into which we write outputs) *)
| output_buffer_484 (** The data sink (into which we write outputs) *)
| output_buffer_485 (** The data sink (into which we write outputs) *)
| output_buffer_486 (** The data sink (into which we write outputs) *)
| output_buffer_487 (** The data sink (into which we write outputs) *)
| output_buffer_488 (** The data sink (into which we write outputs) *)
| output_buffer_489 (** The data sink (into which we write outputs) *)
| output_buffer_490 (** The data sink (into which we write outputs) *)
| output_buffer_491 (** The data sink (into which we write outputs) *)
| output_buffer_492 (** The data sink (into which we write outputs) *)
| output_buffer_493 (** The data sink (into which we write outputs) *)
| output_buffer_494 (** The data sink (into which we write outputs) *)
| output_buffer_495 (** The data sink (into which we write outputs) *)
| output_buffer_496 (** The data sink (into which we write outputs) *)
| output_buffer_497 (** The data sink (into which we write outputs) *)
| output_buffer_498 (** The data sink (into which we write outputs) *)
| output_buffer_499 (** The data sink (into which we write outputs) *)
| output_buffer_500 (** The data sink (into which we write outputs) *)
| output_buffer_501 (** The data sink (into which we write outputs) *)
| output_buffer_502 (** The data sink (into which we write outputs) *)
| output_buffer_503 (** The data sink (into which we write outputs) *)
| output_buffer_504 (** The data sink (into which we write outputs) *)
| output_buffer_505 (** The data sink (into which we write outputs) *)
| output_buffer_506 (** The data sink (into which we write outputs) *)
| output_buffer_507 (** The data sink (into which we write outputs) *)
| output_buffer_508 (** The data sink (into which we write outputs) *)
| output_buffer_509 (** The data sink (into which we write outputs) *)
| output_buffer_510 (** The data sink (into which we write outputs) *)
| output_buffer_511 (** The data sink (into which we write outputs) *)
| output_buffer_512 (** The data sink (into which we write outputs) *)
| output_buffer_513 (** The data sink (into which we write outputs) *)
| output_buffer_514 (** The data sink (into which we write outputs) *)
| output_buffer_515 (** The data sink (into which we write outputs) *)
| output_buffer_516 (** The data sink (into which we write outputs) *)
| output_buffer_517 (** The data sink (into which we write outputs) *)
| output_buffer_518 (** The data sink (into which we write outputs) *)
| output_buffer_519 (** The data sink (into which we write outputs) *)
| output_buffer_520 (** The data sink (into which we write outputs) *)
| output_buffer_521 (** The data sink (into which we write outputs) *)
| output_buffer_522 (** The data sink (into which we write outputs) *)
| output_buffer_523 (** The data sink (into which we write outputs) *)
| output_buffer_524 (** The data sink (into which we write outputs) *)
| output_buffer_525 (** The data sink (into which we write outputs) *)
| output_buffer_526 (** The data sink (into which we write outputs) *)
| output_buffer_527 (** The data sink (into which we write outputs) *)
| output_buffer_528 (** The data sink (into which we write outputs) *)
| output_buffer_529 (** The data sink (into which we write outputs) *)
| output_buffer_530 (** The data sink (into which we write outputs) *)
| output_buffer_531 (** The data sink (into which we write outputs) *)
| output_buffer_532 (** The data sink (into which we write outputs) *)
| output_buffer_533 (** The data sink (into which we write outputs) *)
| output_buffer_534 (** The data sink (into which we write outputs) *)
| output_buffer_535 (** The data sink (into which we write outputs) *)
| output_buffer_536 (** The data sink (into which we write outputs) *)
.

Definition R r :=
  match r with
  | input_buffer  => bits_t sz
  | queue_empty   => bits_t 1
  | queue_data    => bits_t sz
  | output_buffer => bits_t sz
  | output_buffer_1 => bits_t sz
  | output_buffer_2 => bits_t sz
  | output_buffer_3 => bits_t sz
  | output_buffer_4 => bits_t sz
  | output_buffer_5 => bits_t sz
  | output_buffer_6 => bits_t sz
  | output_buffer_7 => bits_t sz
  | output_buffer_8 => bits_t sz
  | output_buffer_9 => bits_t sz
  | output_buffer_10 => bits_t sz
  | output_buffer_11 => bits_t sz
  | output_buffer_12 => bits_t sz
  | output_buffer_13 => bits_t sz
  | output_buffer_14 => bits_t sz
  | output_buffer_15 => bits_t sz
  | output_buffer_16 => bits_t sz
  | output_buffer_17 => bits_t sz
  | output_buffer_18 => bits_t sz
  | output_buffer_19 => bits_t sz
  | output_buffer_20 => bits_t sz
  | output_buffer_21 => bits_t sz
  | output_buffer_22 => bits_t sz
  | output_buffer_23 => bits_t sz
  | output_buffer_24 => bits_t sz
  | output_buffer_25 => bits_t sz
  | output_buffer_26 => bits_t sz
  | output_buffer_27 => bits_t sz
  | output_buffer_28 => bits_t sz
  | output_buffer_29 => bits_t sz
  | output_buffer_30 => bits_t sz
  | output_buffer_31 => bits_t sz
  | output_buffer_32 => bits_t sz
  | output_buffer_33 => bits_t sz
  | output_buffer_34 => bits_t sz
  | output_buffer_35 => bits_t sz
  | output_buffer_36 => bits_t sz
  | output_buffer_37 => bits_t sz
  | output_buffer_38 => bits_t sz
  | output_buffer_39 => bits_t sz
  | output_buffer_40 => bits_t sz
  | output_buffer_41 => bits_t sz
  | output_buffer_42 => bits_t sz
  | output_buffer_43 => bits_t sz
  | output_buffer_44 => bits_t sz
  | output_buffer_45 => bits_t sz
  | output_buffer_46 => bits_t sz
  | output_buffer_47 => bits_t sz
  | output_buffer_48 => bits_t sz
  | output_buffer_49 => bits_t sz
  | output_buffer_50 => bits_t sz
  | output_buffer_51 => bits_t sz
  | output_buffer_52 => bits_t sz
  | output_buffer_53 => bits_t sz
  | output_buffer_54 => bits_t sz
  | output_buffer_55 => bits_t sz
  | output_buffer_56 => bits_t sz
  | output_buffer_57 => bits_t sz
  | output_buffer_58 => bits_t sz
  | output_buffer_59 => bits_t sz
  | output_buffer_60 => bits_t sz
  | output_buffer_61 => bits_t sz
  | output_buffer_62 => bits_t sz
  | output_buffer_63 => bits_t sz
  | output_buffer_64 => bits_t sz
  | output_buffer_65 => bits_t sz
  | output_buffer_66 => bits_t sz
  | output_buffer_67 => bits_t sz
  | output_buffer_68 => bits_t sz
  | output_buffer_69 => bits_t sz
  | output_buffer_70 => bits_t sz
  | output_buffer_71 => bits_t sz
  | output_buffer_72 => bits_t sz
  | output_buffer_73 => bits_t sz
  | output_buffer_74 => bits_t sz
  | output_buffer_75 => bits_t sz
  | output_buffer_76 => bits_t sz
  | output_buffer_77 => bits_t sz
  | output_buffer_78 => bits_t sz
  | output_buffer_79 => bits_t sz
  | output_buffer_80 => bits_t sz
  | output_buffer_81 => bits_t sz
  | output_buffer_82 => bits_t sz
  | output_buffer_83 => bits_t sz
  | output_buffer_84 => bits_t sz
  | output_buffer_85 => bits_t sz
  | output_buffer_86 => bits_t sz
  | output_buffer_87 => bits_t sz
  | output_buffer_88 => bits_t sz
  | output_buffer_89 => bits_t sz
  | output_buffer_90 => bits_t sz
  | output_buffer_91 => bits_t sz
  | output_buffer_92 => bits_t sz
  | output_buffer_93 => bits_t sz
  | output_buffer_94 => bits_t sz
  | output_buffer_95 => bits_t sz
  | output_buffer_96 => bits_t sz
  | output_buffer_97 => bits_t sz
  | output_buffer_98 => bits_t sz
  | output_buffer_99 => bits_t sz
  | output_buffer_100 => bits_t sz
  | output_buffer_101 => bits_t sz
  | output_buffer_102 => bits_t sz
  | output_buffer_103 => bits_t sz
  | output_buffer_104 => bits_t sz
  | output_buffer_105 => bits_t sz
  | output_buffer_106 => bits_t sz
  | output_buffer_107 => bits_t sz
  | output_buffer_108 => bits_t sz
  | output_buffer_109 => bits_t sz
  | output_buffer_110 => bits_t sz
  | output_buffer_111 => bits_t sz
  | output_buffer_112 => bits_t sz
  | output_buffer_113 => bits_t sz
  | output_buffer_114 => bits_t sz
  | output_buffer_115 => bits_t sz
  | output_buffer_116 => bits_t sz
  | output_buffer_117 => bits_t sz
  | output_buffer_118 => bits_t sz
  | output_buffer_119 => bits_t sz
  | output_buffer_120 => bits_t sz
  | output_buffer_121 => bits_t sz
  | output_buffer_122 => bits_t sz
  | output_buffer_123 => bits_t sz
  | output_buffer_124 => bits_t sz
  | output_buffer_125 => bits_t sz
  | output_buffer_126 => bits_t sz
  | output_buffer_127 => bits_t sz
  | output_buffer_128 => bits_t sz
  | output_buffer_129 => bits_t sz
  | output_buffer_130 => bits_t sz
  | output_buffer_131 => bits_t sz
  | output_buffer_132 => bits_t sz
  | output_buffer_133 => bits_t sz
  | output_buffer_134 => bits_t sz
  | output_buffer_135 => bits_t sz
  | output_buffer_136 => bits_t sz
  | output_buffer_137 => bits_t sz
  | output_buffer_138 => bits_t sz
  | output_buffer_139 => bits_t sz
  | output_buffer_140 => bits_t sz
  | output_buffer_141 => bits_t sz
  | output_buffer_142 => bits_t sz
  | output_buffer_143 => bits_t sz
  | output_buffer_144 => bits_t sz
  | output_buffer_145 => bits_t sz
  | output_buffer_146 => bits_t sz
  | output_buffer_147 => bits_t sz
  | output_buffer_148 => bits_t sz
  | output_buffer_149 => bits_t sz
  | output_buffer_150 => bits_t sz
  | output_buffer_151 => bits_t sz
  | output_buffer_152 => bits_t sz
  | output_buffer_153 => bits_t sz
  | output_buffer_154 => bits_t sz
  | output_buffer_155 => bits_t sz
  | output_buffer_156 => bits_t sz
  | output_buffer_157 => bits_t sz
  | output_buffer_158 => bits_t sz
  | output_buffer_159 => bits_t sz
  | output_buffer_160 => bits_t sz
  | output_buffer_161 => bits_t sz
  | output_buffer_162 => bits_t sz
  | output_buffer_163 => bits_t sz
  | output_buffer_164 => bits_t sz
  | output_buffer_165 => bits_t sz
  | output_buffer_166 => bits_t sz
  | output_buffer_167 => bits_t sz
  | output_buffer_168 => bits_t sz
  | output_buffer_169 => bits_t sz
  | output_buffer_170 => bits_t sz
  | output_buffer_171 => bits_t sz
  | output_buffer_172 => bits_t sz
  | output_buffer_173 => bits_t sz
  | output_buffer_174 => bits_t sz
  | output_buffer_175 => bits_t sz
  | output_buffer_176 => bits_t sz
  | output_buffer_177 => bits_t sz
  | output_buffer_178 => bits_t sz
  | output_buffer_179 => bits_t sz
  | output_buffer_180 => bits_t sz
  | output_buffer_181 => bits_t sz
  | output_buffer_182 => bits_t sz
  | output_buffer_183 => bits_t sz
  | output_buffer_184 => bits_t sz
  | output_buffer_185 => bits_t sz
  | output_buffer_186 => bits_t sz
  | output_buffer_187 => bits_t sz
  | output_buffer_188 => bits_t sz
  | output_buffer_189 => bits_t sz
  | output_buffer_190 => bits_t sz
  | output_buffer_191 => bits_t sz
  | output_buffer_192 => bits_t sz
  | output_buffer_193 => bits_t sz
  | output_buffer_194 => bits_t sz
  | output_buffer_195 => bits_t sz
  | output_buffer_196 => bits_t sz
  | output_buffer_197 => bits_t sz
  | output_buffer_198 => bits_t sz
  | output_buffer_199 => bits_t sz
  | output_buffer_200 => bits_t sz
  | output_buffer_201 => bits_t sz
  | output_buffer_202 => bits_t sz
  | output_buffer_203 => bits_t sz
  | output_buffer_204 => bits_t sz
  | output_buffer_205 => bits_t sz
  | output_buffer_206 => bits_t sz
  | output_buffer_207 => bits_t sz
  | output_buffer_208 => bits_t sz
  | output_buffer_209 => bits_t sz
  | output_buffer_210 => bits_t sz
  | output_buffer_211 => bits_t sz
  | output_buffer_212 => bits_t sz
  | output_buffer_213 => bits_t sz
  | output_buffer_214 => bits_t sz
  | output_buffer_215 => bits_t sz
  | output_buffer_216 => bits_t sz
  | output_buffer_217 => bits_t sz
  | output_buffer_218 => bits_t sz
  | output_buffer_219 => bits_t sz
  | output_buffer_220 => bits_t sz
  | output_buffer_221 => bits_t sz
  | output_buffer_222 => bits_t sz
  | output_buffer_223 => bits_t sz
  | output_buffer_224 => bits_t sz
  | output_buffer_225 => bits_t sz
  | output_buffer_226 => bits_t sz
  | output_buffer_227 => bits_t sz
  | output_buffer_228 => bits_t sz
  | output_buffer_229 => bits_t sz
  | output_buffer_230 => bits_t sz
  | output_buffer_231 => bits_t sz
  | output_buffer_232 => bits_t sz
  | output_buffer_233 => bits_t sz
  | output_buffer_234 => bits_t sz
  | output_buffer_235 => bits_t sz
  | output_buffer_236 => bits_t sz
  | output_buffer_237 => bits_t sz
  | output_buffer_238 => bits_t sz
  | output_buffer_239 => bits_t sz
  | output_buffer_240 => bits_t sz
  | output_buffer_241 => bits_t sz
  | output_buffer_242 => bits_t sz
  | output_buffer_243 => bits_t sz
  | output_buffer_244 => bits_t sz
  | output_buffer_245 => bits_t sz
  | output_buffer_246 => bits_t sz
  | output_buffer_247 => bits_t sz
  | output_buffer_248 => bits_t sz
  | output_buffer_249 => bits_t sz
  | output_buffer_250 => bits_t sz
  | output_buffer_251 => bits_t sz
  | output_buffer_252 => bits_t sz
  | output_buffer_253 => bits_t sz
  | output_buffer_254 => bits_t sz
  | output_buffer_255 => bits_t sz
  | output_buffer_256 => bits_t sz
  | output_buffer_257 => bits_t sz
  | output_buffer_258 => bits_t sz
  | output_buffer_259 => bits_t sz
  | output_buffer_260 => bits_t sz
  | output_buffer_261 => bits_t sz
  | output_buffer_262 => bits_t sz
  | output_buffer_263 => bits_t sz
  | output_buffer_264 => bits_t sz
  | output_buffer_265 => bits_t sz
  | output_buffer_266 => bits_t sz
  | output_buffer_267 => bits_t sz
  | output_buffer_268 => bits_t sz
  | output_buffer_269 => bits_t sz
  | output_buffer_270 => bits_t sz
  | output_buffer_271 => bits_t sz
  | output_buffer_272 => bits_t sz
  | output_buffer_273 => bits_t sz
  | output_buffer_274 => bits_t sz
  | output_buffer_275 => bits_t sz
  | output_buffer_276 => bits_t sz
  | output_buffer_277 => bits_t sz
  | output_buffer_278 => bits_t sz
  | output_buffer_279 => bits_t sz
  | output_buffer_280 => bits_t sz
  | output_buffer_281 => bits_t sz
  | output_buffer_282 => bits_t sz
  | output_buffer_283 => bits_t sz
  | output_buffer_284 => bits_t sz
  | output_buffer_285 => bits_t sz
  | output_buffer_286 => bits_t sz
  | output_buffer_287 => bits_t sz
  | output_buffer_288 => bits_t sz
  | output_buffer_289 => bits_t sz
  | output_buffer_290 => bits_t sz
  | output_buffer_291 => bits_t sz
  | output_buffer_292 => bits_t sz
  | output_buffer_293 => bits_t sz
  | output_buffer_294 => bits_t sz
  | output_buffer_295 => bits_t sz
  | output_buffer_296 => bits_t sz
  | output_buffer_297 => bits_t sz
  | output_buffer_298 => bits_t sz
  | output_buffer_299 => bits_t sz
  | output_buffer_300 => bits_t sz
  | output_buffer_301 => bits_t sz
  | output_buffer_302 => bits_t sz
  | output_buffer_303 => bits_t sz
  | output_buffer_304 => bits_t sz
  | output_buffer_305 => bits_t sz
  | output_buffer_306 => bits_t sz
  | output_buffer_307 => bits_t sz
  | output_buffer_308 => bits_t sz
  | output_buffer_309 => bits_t sz
  | output_buffer_310 => bits_t sz
  | output_buffer_311 => bits_t sz
  | output_buffer_312 => bits_t sz
  | output_buffer_313 => bits_t sz
  | output_buffer_314 => bits_t sz
  | output_buffer_315 => bits_t sz
  | output_buffer_316 => bits_t sz
  | output_buffer_317 => bits_t sz
  | output_buffer_318 => bits_t sz
  | output_buffer_319 => bits_t sz
  | output_buffer_320 => bits_t sz
  | output_buffer_321 => bits_t sz
  | output_buffer_322 => bits_t sz
  | output_buffer_323 => bits_t sz
  | output_buffer_324 => bits_t sz
  | output_buffer_325 => bits_t sz
  | output_buffer_326 => bits_t sz
  | output_buffer_327 => bits_t sz
  | output_buffer_328 => bits_t sz
  | output_buffer_329 => bits_t sz
  | output_buffer_330 => bits_t sz
  | output_buffer_331 => bits_t sz
  | output_buffer_332 => bits_t sz
  | output_buffer_333 => bits_t sz
  | output_buffer_334 => bits_t sz
  | output_buffer_335 => bits_t sz
  | output_buffer_336 => bits_t sz
  | output_buffer_337 => bits_t sz
  | output_buffer_338 => bits_t sz
  | output_buffer_339 => bits_t sz
  | output_buffer_340 => bits_t sz
  | output_buffer_341 => bits_t sz
  | output_buffer_342 => bits_t sz
  | output_buffer_343 => bits_t sz
  | output_buffer_344 => bits_t sz
  | output_buffer_345 => bits_t sz
  | output_buffer_346 => bits_t sz
  | output_buffer_347 => bits_t sz
  | output_buffer_348 => bits_t sz
  | output_buffer_349 => bits_t sz
  | output_buffer_350 => bits_t sz
  | output_buffer_351 => bits_t sz
  | output_buffer_352 => bits_t sz
  | output_buffer_353 => bits_t sz
  | output_buffer_354 => bits_t sz
  | output_buffer_355 => bits_t sz
  | output_buffer_356 => bits_t sz
  | output_buffer_357 => bits_t sz
  | output_buffer_358 => bits_t sz
  | output_buffer_359 => bits_t sz
  | output_buffer_360 => bits_t sz
  | output_buffer_361 => bits_t sz
  | output_buffer_362 => bits_t sz
  | output_buffer_363 => bits_t sz
  | output_buffer_364 => bits_t sz
  | output_buffer_365 => bits_t sz
  | output_buffer_366 => bits_t sz
  | output_buffer_367 => bits_t sz
  | output_buffer_368 => bits_t sz
  | output_buffer_369 => bits_t sz
  | output_buffer_370 => bits_t sz
  | output_buffer_371 => bits_t sz
  | output_buffer_372 => bits_t sz
  | output_buffer_373 => bits_t sz
  | output_buffer_374 => bits_t sz
  | output_buffer_375 => bits_t sz
  | output_buffer_376 => bits_t sz
  | output_buffer_377 => bits_t sz
  | output_buffer_378 => bits_t sz
  | output_buffer_379 => bits_t sz
  | output_buffer_380 => bits_t sz
  | output_buffer_381 => bits_t sz
  | output_buffer_382 => bits_t sz
  | output_buffer_383 => bits_t sz
  | output_buffer_384 => bits_t sz
  | output_buffer_385 => bits_t sz
  | output_buffer_386 => bits_t sz
  | output_buffer_387 => bits_t sz
  | output_buffer_388 => bits_t sz
  | output_buffer_389 => bits_t sz
  | output_buffer_390 => bits_t sz
  | output_buffer_391 => bits_t sz
  | output_buffer_392 => bits_t sz
  | output_buffer_393 => bits_t sz
  | output_buffer_394 => bits_t sz
  | output_buffer_395 => bits_t sz
  | output_buffer_396 => bits_t sz
  | output_buffer_397 => bits_t sz
  | output_buffer_398 => bits_t sz
  | output_buffer_399 => bits_t sz
  | output_buffer_400 => bits_t sz
  | output_buffer_401 => bits_t sz
  | output_buffer_402 => bits_t sz
  | output_buffer_403 => bits_t sz
  | output_buffer_404 => bits_t sz
  | output_buffer_405 => bits_t sz
  | output_buffer_406 => bits_t sz
  | output_buffer_407 => bits_t sz
  | output_buffer_408 => bits_t sz
  | output_buffer_409 => bits_t sz
  | output_buffer_410 => bits_t sz
  | output_buffer_411 => bits_t sz
  | output_buffer_412 => bits_t sz
  | output_buffer_413 => bits_t sz
  | output_buffer_414 => bits_t sz
  | output_buffer_415 => bits_t sz
  | output_buffer_416 => bits_t sz
  | output_buffer_417 => bits_t sz
  | output_buffer_418 => bits_t sz
  | output_buffer_419 => bits_t sz
  | output_buffer_420 => bits_t sz
  | output_buffer_421 => bits_t sz
  | output_buffer_422 => bits_t sz
  | output_buffer_423 => bits_t sz
  | output_buffer_424 => bits_t sz
  | output_buffer_425 => bits_t sz
  | output_buffer_426 => bits_t sz
  | output_buffer_427 => bits_t sz
  | output_buffer_428 => bits_t sz
  | output_buffer_429 => bits_t sz
  | output_buffer_430 => bits_t sz
  | output_buffer_431 => bits_t sz
  | output_buffer_432 => bits_t sz
  | output_buffer_433 => bits_t sz
  | output_buffer_434 => bits_t sz
  | output_buffer_435 => bits_t sz
  | output_buffer_436 => bits_t sz
  | output_buffer_437 => bits_t sz
  | output_buffer_438 => bits_t sz
  | output_buffer_439 => bits_t sz
  | output_buffer_440 => bits_t sz
  | output_buffer_441 => bits_t sz
  | output_buffer_442 => bits_t sz
  | output_buffer_443 => bits_t sz
  | output_buffer_444 => bits_t sz
  | output_buffer_445 => bits_t sz
  | output_buffer_446 => bits_t sz
  | output_buffer_447 => bits_t sz
  | output_buffer_448 => bits_t sz
  | output_buffer_449 => bits_t sz
  | output_buffer_450 => bits_t sz
  | output_buffer_451 => bits_t sz
  | output_buffer_452 => bits_t sz
  | output_buffer_453 => bits_t sz
  | output_buffer_454 => bits_t sz
  | output_buffer_455 => bits_t sz
  | output_buffer_456 => bits_t sz
  | output_buffer_457 => bits_t sz
  | output_buffer_458 => bits_t sz
  | output_buffer_459 => bits_t sz
  | output_buffer_460 => bits_t sz
  | output_buffer_461 => bits_t sz
  | output_buffer_462 => bits_t sz
  | output_buffer_463 => bits_t sz
  | output_buffer_464 => bits_t sz
  | output_buffer_465 => bits_t sz
  | output_buffer_466 => bits_t sz
  | output_buffer_467 => bits_t sz
  | output_buffer_468 => bits_t sz
  | output_buffer_469 => bits_t sz
  | output_buffer_470 => bits_t sz
  | output_buffer_471 => bits_t sz
  | output_buffer_472 => bits_t sz
  | output_buffer_473 => bits_t sz
  | output_buffer_474 => bits_t sz
  | output_buffer_475 => bits_t sz
  | output_buffer_476 => bits_t sz
  | output_buffer_477 => bits_t sz
  | output_buffer_478 => bits_t sz
  | output_buffer_479 => bits_t sz
  | output_buffer_480 => bits_t sz
  | output_buffer_481 => bits_t sz
  | output_buffer_482 => bits_t sz
  | output_buffer_483 => bits_t sz
  | output_buffer_484 => bits_t sz
  | output_buffer_485 => bits_t sz
  | output_buffer_486 => bits_t sz
  | output_buffer_487 => bits_t sz
  | output_buffer_488 => bits_t sz
  | output_buffer_489 => bits_t sz
  | output_buffer_490 => bits_t sz
  | output_buffer_491 => bits_t sz
  | output_buffer_492 => bits_t sz
  | output_buffer_493 => bits_t sz
  | output_buffer_494 => bits_t sz
  | output_buffer_495 => bits_t sz
  | output_buffer_496 => bits_t sz
  | output_buffer_497 => bits_t sz
  | output_buffer_498 => bits_t sz
  | output_buffer_499 => bits_t sz
  | output_buffer_500 => bits_t sz
  | output_buffer_501 => bits_t sz
  | output_buffer_502 => bits_t sz
  | output_buffer_503 => bits_t sz
  | output_buffer_504 => bits_t sz
  | output_buffer_505 => bits_t sz
  | output_buffer_506 => bits_t sz
  | output_buffer_507 => bits_t sz
  | output_buffer_508 => bits_t sz
  | output_buffer_509 => bits_t sz
  | output_buffer_510 => bits_t sz
  | output_buffer_511 => bits_t sz
  | output_buffer_512 => bits_t sz
  | output_buffer_513 => bits_t sz
  | output_buffer_514 => bits_t sz
  | output_buffer_515 => bits_t sz
  | output_buffer_516 => bits_t sz
  | output_buffer_517 => bits_t sz
  | output_buffer_518 => bits_t sz
  | output_buffer_519 => bits_t sz
  | output_buffer_520 => bits_t sz
  | output_buffer_521 => bits_t sz
  | output_buffer_522 => bits_t sz
  | output_buffer_523 => bits_t sz
  | output_buffer_524 => bits_t sz
  | output_buffer_525 => bits_t sz
  | output_buffer_526 => bits_t sz
  | output_buffer_527 => bits_t sz
  | output_buffer_528 => bits_t sz
  | output_buffer_529 => bits_t sz
  | output_buffer_530 => bits_t sz
  | output_buffer_531 => bits_t sz
  | output_buffer_532 => bits_t sz
  | output_buffer_533 => bits_t sz
  | output_buffer_534 => bits_t sz
  | output_buffer_535 => bits_t sz
  | output_buffer_536 => bits_t sz
  end.

Inductive ext_fn_t :=
| NextInput (** ``NextInput`` steps through the input stream. **)
| F
| G.

Definition Sigma (fn: ext_fn_t) : ExternalSignature :=
  match fn with
  | NextInput => {$ bits_t sz ~> bits_t sz $}
  | F         => {$ bits_t sz ~> bits_t sz $}
  | G         => {$ bits_t sz ~> bits_t sz $}
  end.

(*|
Then we declare the rules of the system.  Notice how ``doG`` writes at port 0 and ``doF`` reads at port 1.  This is because we're building a pipelined queue, not a bypassing one, so we expect clients to pull first and push second.  Notice also that each rule is "guarded" by a call to ``fail``; that is, if ``doF`` can't push into the queue because ``doG`` is lagging then ``doF`` won't run at all, and if there's no data ready for ``doG`` to consume because ``doF`` isn't keeping up then ``doG`` won't run.
|*)

Arguments Var {pos_t var_t fn_name_t reg_t ext_fn_t R Sigma sig} k {tau m}
: assert.
Definition _doF : uaction reg_t ext_fn_t :=
  {{
     let v := read0(input_buffer) in
     write0(input_buffer, extcall NextInput(v));
     let queue_empty := read1(queue_empty) in
     if queue_empty then
       write1(queue_empty, Ob~0);
       write0(queue_data, extcall F(v))
     else
       fail
  }}.

Definition _doG : uaction _ _ :=
  {{
      let queue_empty := read0(queue_empty) in
      if !queue_empty then
        let data := read0(queue_data) in
        write0(output_buffer, extcall G(data));
        write0(queue_empty, Ob~1)
      else
        fail
  }}.

(*|
Rules are written in an untyped language, so we need to typecheck them, which is done using ``tc_rules``:
|*)

Inductive rule_name_t :=
| doF
| doG.

Definition rules : rule_name_t -> rule R Sigma :=
  Eval vm_compute in
    tc_rules R Sigma
             (fun rl => match rl with
                     | doF => _doF
                     | doG => _doG
                     end).

(*|
The last step if to define the system's scheduler.  Note that we perform ``doG`` before ``doF`` (intuitively, pipelines run back-to-front: in a sequential model, G removes the data found in the queue and writes it to the output, then F reads the input and writes it in the queue).
|*)

Definition pipeline : scheduler :=
  doG |> doF |> done.

(*|
That's it, we've defined our program!  There are a few things we can do with it now.

Running our program
===================

Kôika's semantics are deterministic, so we can simply run the program using the interpreter.  For this we need to define two provide two additional pieces: the value of the registers at the beginning of the cycle (``r``), and a model of the external functions (``σ``).

For the registers, we start with an empty queue, the input set to 32'd1, and the output set to 32'd0.  The notation ``#{ reg => val #}`` indicates that register ``reg`` maps to value ``val``.  Notations like ``Ob~1~0~0~1`` denote bitstring constants: for example, ``Ob~0~1~1`` is the Kôika equivalent of ``3'b011`` in Verilog.
|*)

(** We need [reg_t] to be finite to construct register maps. *)
Instance FiniteType_reg_t : FiniteType reg_t := _.

Definition r : ContextEnv.(env_t) R :=
  #{ input_buffer  => Bits.of_nat 32 1;
     queue_empty   => Ob~1;
     queue_data    => Bits.of_nat 32 0;
     output_buffer => Bits.of_nat 32 0;
     output_buffer_1 => Bits.of_nat 32 0;
     output_buffer_2 => Bits.of_nat 32 0;
     output_buffer_3 => Bits.of_nat 32 0;
     output_buffer_4 => Bits.of_nat 32 0;
     output_buffer_5 => Bits.of_nat 32 0;
     output_buffer_6 => Bits.of_nat 32 0;
     output_buffer_7 => Bits.of_nat 32 0;
     output_buffer_8 => Bits.of_nat 32 0;
     output_buffer_9 => Bits.of_nat 32 0;
     output_buffer_10 => Bits.of_nat 32 0;
     output_buffer_11 => Bits.of_nat 32 0;
     output_buffer_12 => Bits.of_nat 32 0;
     output_buffer_13 => Bits.of_nat 32 0;
     output_buffer_14 => Bits.of_nat 32 0;
     output_buffer_15 => Bits.of_nat 32 0;
     output_buffer_16 => Bits.of_nat 32 0;
     output_buffer_17 => Bits.of_nat 32 0;
     output_buffer_18 => Bits.of_nat 32 0;
     output_buffer_19 => Bits.of_nat 32 0;
     output_buffer_20 => Bits.of_nat 32 0;
     output_buffer_21 => Bits.of_nat 32 0;
     output_buffer_22 => Bits.of_nat 32 0;
     output_buffer_23 => Bits.of_nat 32 0;
     output_buffer_24 => Bits.of_nat 32 0;
     output_buffer_25 => Bits.of_nat 32 0;
     output_buffer_26 => Bits.of_nat 32 0;
     output_buffer_27 => Bits.of_nat 32 0;
     output_buffer_28 => Bits.of_nat 32 0;
     output_buffer_29 => Bits.of_nat 32 0;
     output_buffer_30 => Bits.of_nat 32 0;
     output_buffer_31 => Bits.of_nat 32 0;
     output_buffer_32 => Bits.of_nat 32 0;
     output_buffer_33 => Bits.of_nat 32 0;
     output_buffer_34 => Bits.of_nat 32 0;
     output_buffer_35 => Bits.of_nat 32 0;
     output_buffer_36 => Bits.of_nat 32 0;
     output_buffer_37 => Bits.of_nat 32 0;
     output_buffer_38 => Bits.of_nat 32 0;
     output_buffer_39 => Bits.of_nat 32 0;
     output_buffer_40 => Bits.of_nat 32 0;
     output_buffer_41 => Bits.of_nat 32 0;
     output_buffer_42 => Bits.of_nat 32 0;
     output_buffer_43 => Bits.of_nat 32 0;
     output_buffer_44 => Bits.of_nat 32 0;
     output_buffer_45 => Bits.of_nat 32 0;
     output_buffer_46 => Bits.of_nat 32 0;
     output_buffer_47 => Bits.of_nat 32 0;
     output_buffer_48 => Bits.of_nat 32 0;
     output_buffer_49 => Bits.of_nat 32 0;
     output_buffer_50 => Bits.of_nat 32 0;
     output_buffer_51 => Bits.of_nat 32 0;
     output_buffer_52 => Bits.of_nat 32 0;
     output_buffer_53 => Bits.of_nat 32 0;
     output_buffer_54 => Bits.of_nat 32 0;
     output_buffer_55 => Bits.of_nat 32 0;
     output_buffer_56 => Bits.of_nat 32 0;
     output_buffer_57 => Bits.of_nat 32 0;
     output_buffer_58 => Bits.of_nat 32 0;
     output_buffer_59 => Bits.of_nat 32 0;
     output_buffer_60 => Bits.of_nat 32 0;
     output_buffer_61 => Bits.of_nat 32 0;
     output_buffer_62 => Bits.of_nat 32 0;
     output_buffer_63 => Bits.of_nat 32 0;
     output_buffer_64 => Bits.of_nat 32 0;
     output_buffer_65 => Bits.of_nat 32 0;
     output_buffer_66 => Bits.of_nat 32 0;
     output_buffer_67 => Bits.of_nat 32 0;
     output_buffer_68 => Bits.of_nat 32 0;
     output_buffer_69 => Bits.of_nat 32 0;
     output_buffer_70 => Bits.of_nat 32 0;
     output_buffer_71 => Bits.of_nat 32 0;
     output_buffer_72 => Bits.of_nat 32 0;
     output_buffer_73 => Bits.of_nat 32 0;
     output_buffer_74 => Bits.of_nat 32 0;
     output_buffer_75 => Bits.of_nat 32 0;
     output_buffer_76 => Bits.of_nat 32 0;
     output_buffer_77 => Bits.of_nat 32 0;
     output_buffer_78 => Bits.of_nat 32 0;
     output_buffer_79 => Bits.of_nat 32 0;
     output_buffer_80 => Bits.of_nat 32 0;
     output_buffer_81 => Bits.of_nat 32 0;
     output_buffer_82 => Bits.of_nat 32 0;
     output_buffer_83 => Bits.of_nat 32 0;
     output_buffer_84 => Bits.of_nat 32 0;
     output_buffer_85 => Bits.of_nat 32 0;
     output_buffer_86 => Bits.of_nat 32 0;
     output_buffer_87 => Bits.of_nat 32 0;
     output_buffer_88 => Bits.of_nat 32 0;
     output_buffer_89 => Bits.of_nat 32 0;
     output_buffer_90 => Bits.of_nat 32 0;
     output_buffer_91 => Bits.of_nat 32 0;
     output_buffer_92 => Bits.of_nat 32 0;
     output_buffer_93 => Bits.of_nat 32 0;
     output_buffer_94 => Bits.of_nat 32 0;
     output_buffer_95 => Bits.of_nat 32 0;
     output_buffer_96 => Bits.of_nat 32 0;
     output_buffer_97 => Bits.of_nat 32 0;
     output_buffer_98 => Bits.of_nat 32 0;
     output_buffer_99 => Bits.of_nat 32 0;
     output_buffer_100 => Bits.of_nat 32 0;
     output_buffer_101 => Bits.of_nat 32 0;
     output_buffer_102 => Bits.of_nat 32 0;
     output_buffer_103 => Bits.of_nat 32 0;
     output_buffer_104 => Bits.of_nat 32 0;
     output_buffer_105 => Bits.of_nat 32 0;
     output_buffer_106 => Bits.of_nat 32 0;
     output_buffer_107 => Bits.of_nat 32 0;
     output_buffer_108 => Bits.of_nat 32 0;
     output_buffer_109 => Bits.of_nat 32 0;
     output_buffer_110 => Bits.of_nat 32 0;
     output_buffer_111 => Bits.of_nat 32 0;
     output_buffer_112 => Bits.of_nat 32 0;
     output_buffer_113 => Bits.of_nat 32 0;
     output_buffer_114 => Bits.of_nat 32 0;
     output_buffer_115 => Bits.of_nat 32 0;
     output_buffer_116 => Bits.of_nat 32 0;
     output_buffer_117 => Bits.of_nat 32 0;
     output_buffer_118 => Bits.of_nat 32 0;
     output_buffer_119 => Bits.of_nat 32 0;
     output_buffer_120 => Bits.of_nat 32 0;
     output_buffer_121 => Bits.of_nat 32 0;
     output_buffer_122 => Bits.of_nat 32 0;
     output_buffer_123 => Bits.of_nat 32 0;
     output_buffer_124 => Bits.of_nat 32 0;
     output_buffer_125 => Bits.of_nat 32 0;
     output_buffer_126 => Bits.of_nat 32 0;
     output_buffer_127 => Bits.of_nat 32 0;
     output_buffer_128 => Bits.of_nat 32 0;
     output_buffer_129 => Bits.of_nat 32 0;
     output_buffer_130 => Bits.of_nat 32 0;
     output_buffer_131 => Bits.of_nat 32 0;
     output_buffer_132 => Bits.of_nat 32 0;
     output_buffer_133 => Bits.of_nat 32 0;
     output_buffer_134 => Bits.of_nat 32 0;
     output_buffer_135 => Bits.of_nat 32 0;
     output_buffer_136 => Bits.of_nat 32 0;
     output_buffer_137 => Bits.of_nat 32 0;
     output_buffer_138 => Bits.of_nat 32 0;
     output_buffer_139 => Bits.of_nat 32 0;
     output_buffer_140 => Bits.of_nat 32 0;
     output_buffer_141 => Bits.of_nat 32 0;
     output_buffer_142 => Bits.of_nat 32 0;
     output_buffer_143 => Bits.of_nat 32 0;
     output_buffer_144 => Bits.of_nat 32 0;
     output_buffer_145 => Bits.of_nat 32 0;
     output_buffer_146 => Bits.of_nat 32 0;
     output_buffer_147 => Bits.of_nat 32 0;
     output_buffer_148 => Bits.of_nat 32 0;
     output_buffer_149 => Bits.of_nat 32 0;
     output_buffer_150 => Bits.of_nat 32 0;
     output_buffer_151 => Bits.of_nat 32 0;
     output_buffer_152 => Bits.of_nat 32 0;
     output_buffer_153 => Bits.of_nat 32 0;
     output_buffer_154 => Bits.of_nat 32 0;
     output_buffer_155 => Bits.of_nat 32 0;
     output_buffer_156 => Bits.of_nat 32 0;
     output_buffer_157 => Bits.of_nat 32 0;
     output_buffer_158 => Bits.of_nat 32 0;
     output_buffer_159 => Bits.of_nat 32 0;
     output_buffer_160 => Bits.of_nat 32 0;
     output_buffer_161 => Bits.of_nat 32 0;
     output_buffer_162 => Bits.of_nat 32 0;
     output_buffer_163 => Bits.of_nat 32 0;
     output_buffer_164 => Bits.of_nat 32 0;
     output_buffer_165 => Bits.of_nat 32 0;
     output_buffer_166 => Bits.of_nat 32 0;
     output_buffer_167 => Bits.of_nat 32 0;
     output_buffer_168 => Bits.of_nat 32 0;
     output_buffer_169 => Bits.of_nat 32 0;
     output_buffer_170 => Bits.of_nat 32 0;
     output_buffer_171 => Bits.of_nat 32 0;
     output_buffer_172 => Bits.of_nat 32 0;
     output_buffer_173 => Bits.of_nat 32 0;
     output_buffer_174 => Bits.of_nat 32 0;
     output_buffer_175 => Bits.of_nat 32 0;
     output_buffer_176 => Bits.of_nat 32 0;
     output_buffer_177 => Bits.of_nat 32 0;
     output_buffer_178 => Bits.of_nat 32 0;
     output_buffer_179 => Bits.of_nat 32 0;
     output_buffer_180 => Bits.of_nat 32 0;
     output_buffer_181 => Bits.of_nat 32 0;
     output_buffer_182 => Bits.of_nat 32 0;
     output_buffer_183 => Bits.of_nat 32 0;
     output_buffer_184 => Bits.of_nat 32 0;
     output_buffer_185 => Bits.of_nat 32 0;
     output_buffer_186 => Bits.of_nat 32 0;
     output_buffer_187 => Bits.of_nat 32 0;
     output_buffer_188 => Bits.of_nat 32 0;
     output_buffer_189 => Bits.of_nat 32 0;
     output_buffer_190 => Bits.of_nat 32 0;
     output_buffer_191 => Bits.of_nat 32 0;
     output_buffer_192 => Bits.of_nat 32 0;
     output_buffer_193 => Bits.of_nat 32 0;
     output_buffer_194 => Bits.of_nat 32 0;
     output_buffer_195 => Bits.of_nat 32 0;
     output_buffer_196 => Bits.of_nat 32 0;
     output_buffer_197 => Bits.of_nat 32 0;
     output_buffer_198 => Bits.of_nat 32 0;
     output_buffer_199 => Bits.of_nat 32 0;
     output_buffer_200 => Bits.of_nat 32 0;
     output_buffer_201 => Bits.of_nat 32 0;
     output_buffer_202 => Bits.of_nat 32 0;
     output_buffer_203 => Bits.of_nat 32 0;
     output_buffer_204 => Bits.of_nat 32 0;
     output_buffer_205 => Bits.of_nat 32 0;
     output_buffer_206 => Bits.of_nat 32 0;
     output_buffer_207 => Bits.of_nat 32 0;
     output_buffer_208 => Bits.of_nat 32 0;
     output_buffer_209 => Bits.of_nat 32 0;
     output_buffer_210 => Bits.of_nat 32 0;
     output_buffer_211 => Bits.of_nat 32 0;
     output_buffer_212 => Bits.of_nat 32 0;
     output_buffer_213 => Bits.of_nat 32 0;
     output_buffer_214 => Bits.of_nat 32 0;
     output_buffer_215 => Bits.of_nat 32 0;
     output_buffer_216 => Bits.of_nat 32 0;
     output_buffer_217 => Bits.of_nat 32 0;
     output_buffer_218 => Bits.of_nat 32 0;
     output_buffer_219 => Bits.of_nat 32 0;
     output_buffer_220 => Bits.of_nat 32 0;
     output_buffer_221 => Bits.of_nat 32 0;
     output_buffer_222 => Bits.of_nat 32 0;
     output_buffer_223 => Bits.of_nat 32 0;
     output_buffer_224 => Bits.of_nat 32 0;
     output_buffer_225 => Bits.of_nat 32 0;
     output_buffer_226 => Bits.of_nat 32 0;
     output_buffer_227 => Bits.of_nat 32 0;
     output_buffer_228 => Bits.of_nat 32 0;
     output_buffer_229 => Bits.of_nat 32 0;
     output_buffer_230 => Bits.of_nat 32 0;
     output_buffer_231 => Bits.of_nat 32 0;
     output_buffer_232 => Bits.of_nat 32 0;
     output_buffer_233 => Bits.of_nat 32 0;
     output_buffer_234 => Bits.of_nat 32 0;
     output_buffer_235 => Bits.of_nat 32 0;
     output_buffer_236 => Bits.of_nat 32 0;
     output_buffer_237 => Bits.of_nat 32 0;
     output_buffer_238 => Bits.of_nat 32 0;
     output_buffer_239 => Bits.of_nat 32 0;
     output_buffer_240 => Bits.of_nat 32 0;
     output_buffer_241 => Bits.of_nat 32 0;
     output_buffer_242 => Bits.of_nat 32 0;
     output_buffer_243 => Bits.of_nat 32 0;
     output_buffer_244 => Bits.of_nat 32 0;
     output_buffer_245 => Bits.of_nat 32 0;
     output_buffer_246 => Bits.of_nat 32 0;
     output_buffer_247 => Bits.of_nat 32 0;
     output_buffer_248 => Bits.of_nat 32 0;
     output_buffer_249 => Bits.of_nat 32 0;
     output_buffer_250 => Bits.of_nat 32 0;
     output_buffer_251 => Bits.of_nat 32 0;
     output_buffer_252 => Bits.of_nat 32 0;
     output_buffer_253 => Bits.of_nat 32 0;
     output_buffer_254 => Bits.of_nat 32 0;
     output_buffer_255 => Bits.of_nat 32 0;
     output_buffer_256 => Bits.of_nat 32 0;
     output_buffer_257 => Bits.of_nat 32 0;
     output_buffer_258 => Bits.of_nat 32 0;
     output_buffer_259 => Bits.of_nat 32 0;
     output_buffer_260 => Bits.of_nat 32 0;
     output_buffer_261 => Bits.of_nat 32 0;
     output_buffer_262 => Bits.of_nat 32 0;
     output_buffer_263 => Bits.of_nat 32 0;
     output_buffer_264 => Bits.of_nat 32 0;
     output_buffer_265 => Bits.of_nat 32 0;
     output_buffer_266 => Bits.of_nat 32 0;
     output_buffer_267 => Bits.of_nat 32 0;
     output_buffer_268 => Bits.of_nat 32 0;
     output_buffer_269 => Bits.of_nat 32 0;
     output_buffer_270 => Bits.of_nat 32 0;
     output_buffer_271 => Bits.of_nat 32 0;
     output_buffer_272 => Bits.of_nat 32 0;
     output_buffer_273 => Bits.of_nat 32 0;
     output_buffer_274 => Bits.of_nat 32 0;
     output_buffer_275 => Bits.of_nat 32 0;
     output_buffer_276 => Bits.of_nat 32 0;
     output_buffer_277 => Bits.of_nat 32 0;
     output_buffer_278 => Bits.of_nat 32 0;
     output_buffer_279 => Bits.of_nat 32 0;
     output_buffer_280 => Bits.of_nat 32 0;
     output_buffer_281 => Bits.of_nat 32 0;
     output_buffer_282 => Bits.of_nat 32 0;
     output_buffer_283 => Bits.of_nat 32 0;
     output_buffer_284 => Bits.of_nat 32 0;
     output_buffer_285 => Bits.of_nat 32 0;
     output_buffer_286 => Bits.of_nat 32 0;
     output_buffer_287 => Bits.of_nat 32 0;
     output_buffer_288 => Bits.of_nat 32 0;
     output_buffer_289 => Bits.of_nat 32 0;
     output_buffer_290 => Bits.of_nat 32 0;
     output_buffer_291 => Bits.of_nat 32 0;
     output_buffer_292 => Bits.of_nat 32 0;
     output_buffer_293 => Bits.of_nat 32 0;
     output_buffer_294 => Bits.of_nat 32 0;
     output_buffer_295 => Bits.of_nat 32 0;
     output_buffer_296 => Bits.of_nat 32 0;
     output_buffer_297 => Bits.of_nat 32 0;
     output_buffer_298 => Bits.of_nat 32 0;
     output_buffer_299 => Bits.of_nat 32 0;
     output_buffer_300 => Bits.of_nat 32 0;
     output_buffer_301 => Bits.of_nat 32 0;
     output_buffer_302 => Bits.of_nat 32 0;
     output_buffer_303 => Bits.of_nat 32 0;
     output_buffer_304 => Bits.of_nat 32 0;
     output_buffer_305 => Bits.of_nat 32 0;
     output_buffer_306 => Bits.of_nat 32 0;
     output_buffer_307 => Bits.of_nat 32 0;
     output_buffer_308 => Bits.of_nat 32 0;
     output_buffer_309 => Bits.of_nat 32 0;
     output_buffer_310 => Bits.of_nat 32 0;
     output_buffer_311 => Bits.of_nat 32 0;
     output_buffer_312 => Bits.of_nat 32 0;
     output_buffer_313 => Bits.of_nat 32 0;
     output_buffer_314 => Bits.of_nat 32 0;
     output_buffer_315 => Bits.of_nat 32 0;
     output_buffer_316 => Bits.of_nat 32 0;
     output_buffer_317 => Bits.of_nat 32 0;
     output_buffer_318 => Bits.of_nat 32 0;
     output_buffer_319 => Bits.of_nat 32 0;
     output_buffer_320 => Bits.of_nat 32 0;
     output_buffer_321 => Bits.of_nat 32 0;
     output_buffer_322 => Bits.of_nat 32 0;
     output_buffer_323 => Bits.of_nat 32 0;
     output_buffer_324 => Bits.of_nat 32 0;
     output_buffer_325 => Bits.of_nat 32 0;
     output_buffer_326 => Bits.of_nat 32 0;
     output_buffer_327 => Bits.of_nat 32 0;
     output_buffer_328 => Bits.of_nat 32 0;
     output_buffer_329 => Bits.of_nat 32 0;
     output_buffer_330 => Bits.of_nat 32 0;
     output_buffer_331 => Bits.of_nat 32 0;
     output_buffer_332 => Bits.of_nat 32 0;
     output_buffer_333 => Bits.of_nat 32 0;
     output_buffer_334 => Bits.of_nat 32 0;
     output_buffer_335 => Bits.of_nat 32 0;
     output_buffer_336 => Bits.of_nat 32 0;
     output_buffer_337 => Bits.of_nat 32 0;
     output_buffer_338 => Bits.of_nat 32 0;
     output_buffer_339 => Bits.of_nat 32 0;
     output_buffer_340 => Bits.of_nat 32 0;
     output_buffer_341 => Bits.of_nat 32 0;
     output_buffer_342 => Bits.of_nat 32 0;
     output_buffer_343 => Bits.of_nat 32 0;
     output_buffer_344 => Bits.of_nat 32 0;
     output_buffer_345 => Bits.of_nat 32 0;
     output_buffer_346 => Bits.of_nat 32 0;
     output_buffer_347 => Bits.of_nat 32 0;
     output_buffer_348 => Bits.of_nat 32 0;
     output_buffer_349 => Bits.of_nat 32 0;
     output_buffer_350 => Bits.of_nat 32 0;
     output_buffer_351 => Bits.of_nat 32 0;
     output_buffer_352 => Bits.of_nat 32 0;
     output_buffer_353 => Bits.of_nat 32 0;
     output_buffer_354 => Bits.of_nat 32 0;
     output_buffer_355 => Bits.of_nat 32 0;
     output_buffer_356 => Bits.of_nat 32 0;
     output_buffer_357 => Bits.of_nat 32 0;
     output_buffer_358 => Bits.of_nat 32 0;
     output_buffer_359 => Bits.of_nat 32 0;
     output_buffer_360 => Bits.of_nat 32 0;
     output_buffer_361 => Bits.of_nat 32 0;
     output_buffer_362 => Bits.of_nat 32 0;
     output_buffer_363 => Bits.of_nat 32 0;
     output_buffer_364 => Bits.of_nat 32 0;
     output_buffer_365 => Bits.of_nat 32 0;
     output_buffer_366 => Bits.of_nat 32 0;
     output_buffer_367 => Bits.of_nat 32 0;
     output_buffer_368 => Bits.of_nat 32 0;
     output_buffer_369 => Bits.of_nat 32 0;
     output_buffer_370 => Bits.of_nat 32 0;
     output_buffer_371 => Bits.of_nat 32 0;
     output_buffer_372 => Bits.of_nat 32 0;
     output_buffer_373 => Bits.of_nat 32 0;
     output_buffer_374 => Bits.of_nat 32 0;
     output_buffer_375 => Bits.of_nat 32 0;
     output_buffer_376 => Bits.of_nat 32 0;
     output_buffer_377 => Bits.of_nat 32 0;
     output_buffer_378 => Bits.of_nat 32 0;
     output_buffer_379 => Bits.of_nat 32 0;
     output_buffer_380 => Bits.of_nat 32 0;
     output_buffer_381 => Bits.of_nat 32 0;
     output_buffer_382 => Bits.of_nat 32 0;
     output_buffer_383 => Bits.of_nat 32 0;
     output_buffer_384 => Bits.of_nat 32 0;
     output_buffer_385 => Bits.of_nat 32 0;
     output_buffer_386 => Bits.of_nat 32 0;
     output_buffer_387 => Bits.of_nat 32 0;
     output_buffer_388 => Bits.of_nat 32 0;
     output_buffer_389 => Bits.of_nat 32 0;
     output_buffer_390 => Bits.of_nat 32 0;
     output_buffer_391 => Bits.of_nat 32 0;
     output_buffer_392 => Bits.of_nat 32 0;
     output_buffer_393 => Bits.of_nat 32 0;
     output_buffer_394 => Bits.of_nat 32 0;
     output_buffer_395 => Bits.of_nat 32 0;
     output_buffer_396 => Bits.of_nat 32 0;
     output_buffer_397 => Bits.of_nat 32 0;
     output_buffer_398 => Bits.of_nat 32 0;
     output_buffer_399 => Bits.of_nat 32 0;
     output_buffer_400 => Bits.of_nat 32 0;
     output_buffer_401 => Bits.of_nat 32 0;
     output_buffer_402 => Bits.of_nat 32 0;
     output_buffer_403 => Bits.of_nat 32 0;
     output_buffer_404 => Bits.of_nat 32 0;
     output_buffer_405 => Bits.of_nat 32 0;
     output_buffer_406 => Bits.of_nat 32 0;
     output_buffer_407 => Bits.of_nat 32 0;
     output_buffer_408 => Bits.of_nat 32 0;
     output_buffer_409 => Bits.of_nat 32 0;
     output_buffer_410 => Bits.of_nat 32 0;
     output_buffer_411 => Bits.of_nat 32 0;
     output_buffer_412 => Bits.of_nat 32 0;
     output_buffer_413 => Bits.of_nat 32 0;
     output_buffer_414 => Bits.of_nat 32 0;
     output_buffer_415 => Bits.of_nat 32 0;
     output_buffer_416 => Bits.of_nat 32 0;
     output_buffer_417 => Bits.of_nat 32 0;
     output_buffer_418 => Bits.of_nat 32 0;
     output_buffer_419 => Bits.of_nat 32 0;
     output_buffer_420 => Bits.of_nat 32 0;
     output_buffer_421 => Bits.of_nat 32 0;
     output_buffer_422 => Bits.of_nat 32 0;
     output_buffer_423 => Bits.of_nat 32 0;
     output_buffer_424 => Bits.of_nat 32 0;
     output_buffer_425 => Bits.of_nat 32 0;
     output_buffer_426 => Bits.of_nat 32 0;
     output_buffer_427 => Bits.of_nat 32 0;
     output_buffer_428 => Bits.of_nat 32 0;
     output_buffer_429 => Bits.of_nat 32 0;
     output_buffer_430 => Bits.of_nat 32 0;
     output_buffer_431 => Bits.of_nat 32 0;
     output_buffer_432 => Bits.of_nat 32 0;
     output_buffer_433 => Bits.of_nat 32 0;
     output_buffer_434 => Bits.of_nat 32 0;
     output_buffer_435 => Bits.of_nat 32 0;
     output_buffer_436 => Bits.of_nat 32 0;
     output_buffer_437 => Bits.of_nat 32 0;
     output_buffer_438 => Bits.of_nat 32 0;
     output_buffer_439 => Bits.of_nat 32 0;
     output_buffer_440 => Bits.of_nat 32 0;
     output_buffer_441 => Bits.of_nat 32 0;
     output_buffer_442 => Bits.of_nat 32 0;
     output_buffer_443 => Bits.of_nat 32 0;
     output_buffer_444 => Bits.of_nat 32 0;
     output_buffer_445 => Bits.of_nat 32 0;
     output_buffer_446 => Bits.of_nat 32 0;
     output_buffer_447 => Bits.of_nat 32 0;
     output_buffer_448 => Bits.of_nat 32 0;
     output_buffer_449 => Bits.of_nat 32 0;
     output_buffer_450 => Bits.of_nat 32 0;
     output_buffer_451 => Bits.of_nat 32 0;
     output_buffer_452 => Bits.of_nat 32 0;
     output_buffer_453 => Bits.of_nat 32 0;
     output_buffer_454 => Bits.of_nat 32 0;
     output_buffer_455 => Bits.of_nat 32 0;
     output_buffer_456 => Bits.of_nat 32 0;
     output_buffer_457 => Bits.of_nat 32 0;
     output_buffer_458 => Bits.of_nat 32 0;
     output_buffer_459 => Bits.of_nat 32 0;
     output_buffer_460 => Bits.of_nat 32 0;
     output_buffer_461 => Bits.of_nat 32 0;
     output_buffer_462 => Bits.of_nat 32 0;
     output_buffer_463 => Bits.of_nat 32 0;
     output_buffer_464 => Bits.of_nat 32 0;
     output_buffer_465 => Bits.of_nat 32 0;
     output_buffer_466 => Bits.of_nat 32 0;
     output_buffer_467 => Bits.of_nat 32 0;
     output_buffer_468 => Bits.of_nat 32 0;
     output_buffer_469 => Bits.of_nat 32 0;
     output_buffer_470 => Bits.of_nat 32 0;
     output_buffer_471 => Bits.of_nat 32 0;
     output_buffer_472 => Bits.of_nat 32 0;
     output_buffer_473 => Bits.of_nat 32 0;
     output_buffer_474 => Bits.of_nat 32 0;
     output_buffer_475 => Bits.of_nat 32 0;
     output_buffer_476 => Bits.of_nat 32 0;
     output_buffer_477 => Bits.of_nat 32 0;
     output_buffer_478 => Bits.of_nat 32 0;
     output_buffer_479 => Bits.of_nat 32 0;
     output_buffer_480 => Bits.of_nat 32 0;
     output_buffer_481 => Bits.of_nat 32 0;
     output_buffer_482 => Bits.of_nat 32 0;
     output_buffer_483 => Bits.of_nat 32 0;
     output_buffer_484 => Bits.of_nat 32 0;
     output_buffer_485 => Bits.of_nat 32 0;
     output_buffer_486 => Bits.of_nat 32 0;
     output_buffer_487 => Bits.of_nat 32 0;
     output_buffer_488 => Bits.of_nat 32 0;
     output_buffer_489 => Bits.of_nat 32 0;
     output_buffer_490 => Bits.of_nat 32 0;
     output_buffer_491 => Bits.of_nat 32 0;
     output_buffer_492 => Bits.of_nat 32 0;
     output_buffer_493 => Bits.of_nat 32 0;
     output_buffer_494 => Bits.of_nat 32 0;
     output_buffer_495 => Bits.of_nat 32 0;
     output_buffer_496 => Bits.of_nat 32 0;
     output_buffer_497 => Bits.of_nat 32 0;
     output_buffer_498 => Bits.of_nat 32 0;
     output_buffer_499 => Bits.of_nat 32 0;
     output_buffer_500 => Bits.of_nat 32 0;
     output_buffer_501 => Bits.of_nat 32 0;
     output_buffer_502 => Bits.of_nat 32 0;
     output_buffer_503 => Bits.of_nat 32 0;
     output_buffer_504 => Bits.of_nat 32 0;
     output_buffer_505 => Bits.of_nat 32 0;
     output_buffer_506 => Bits.of_nat 32 0;
     output_buffer_507 => Bits.of_nat 32 0;
     output_buffer_508 => Bits.of_nat 32 0;
     output_buffer_509 => Bits.of_nat 32 0;
     output_buffer_510 => Bits.of_nat 32 0;
     output_buffer_511 => Bits.of_nat 32 0;
     output_buffer_512 => Bits.of_nat 32 0;
     output_buffer_513 => Bits.of_nat 32 0;
     output_buffer_514 => Bits.of_nat 32 0;
     output_buffer_515 => Bits.of_nat 32 0;
     output_buffer_516 => Bits.of_nat 32 0;
     output_buffer_517 => Bits.of_nat 32 0;
     output_buffer_518 => Bits.of_nat 32 0;
     output_buffer_519 => Bits.of_nat 32 0;
     output_buffer_520 => Bits.of_nat 32 0;
     output_buffer_521 => Bits.of_nat 32 0;
     output_buffer_522 => Bits.of_nat 32 0;
     output_buffer_523 => Bits.of_nat 32 0;
     output_buffer_524 => Bits.of_nat 32 0;
     output_buffer_525 => Bits.of_nat 32 0;
     output_buffer_526 => Bits.of_nat 32 0;
     output_buffer_527 => Bits.of_nat 32 0;
     output_buffer_528 => Bits.of_nat 32 0;
     output_buffer_529 => Bits.of_nat 32 0;
     output_buffer_530 => Bits.of_nat 32 0;
     output_buffer_531 => Bits.of_nat 32 0;
     output_buffer_532 => Bits.of_nat 32 0;
     output_buffer_533 => Bits.of_nat 32 0;
     output_buffer_534 => Bits.of_nat 32 0;
     output_buffer_535 => Bits.of_nat 32 0;
     output_buffer_536 => Bits.of_nat 32 0
  }#.

Require Import BitsToLists.
Definition f_init := fun x => BitsToLists.val_of_value (r.[x]).
Definition initial_context_env_val := ContextEnv.(create) (f_init).
Time Compute initial_context_env_val.
Print type.
Time Compute @BitsToLists.val_of_value (bits_t 32000) (Bits.of_nat 32000 1).
(*|
For the external functions, we take something simple: ``f`` multiplies its input by 5, ``g`` adds one to its input, and ``next_input`` models the sequence of odd numbers ``1, 3, 5, 7, 9, …``:
|*)

Definition σ fn : Sig_denote (Sigma fn) :=
  match fn with
  | NextInput => fun x => x +b (Bits.of_nat 32 2)
  | F         => fun x => Bits.slice 0 32 (x *b (Bits.of_nat 32 5))
  | G         => fun x => x +b (Bits.of_nat 32 1)
  end.

(*|
In the first step of execution ``doG`` does not execute and ``doF`` reads 1 from the input and writes 5 (32'b101) in the queue; the input then becomes 3 (32'b11).

The function ``interp_cycle`` computes this update: it returns a map of register values.
|*)

Compute (UntypedSemantics.interp_cycle σ rules pipeline r). (* .unfold *)

(*|
Here is an infinite stream capturing the initial state of the system and all snapshots of the system after each execution:
|*)

Definition system_states :=
  Streams.coiterate (interp_cycle σ rules pipeline) r.

(*|
Forcing this infinite stream simulates the whole system directly inside Coq: for example, we can easily extract the first few inputs that the system processes, and the first few outputs that it produces:

- Inputs (``1``; ``3``; ``5``; ``7``; ``9``; ``…``):
  ..
|*)

Compute (Streams.firstn 5
           (Streams.map (fun r => r.[input_buffer])
                        system_states)). (* .unfold *)
Compute (Streams.firstn 5
           (Streams.map (fun r => @Bits.to_nat 32 r.[input_buffer])
                        system_states)). (* .unfold *)

(*|
- Outputs (``1 * 5 + 1 = 6``; ``3 * 5 + 1 = 16``; ``5 * 5 + 1 = 26``; ``…``); the first two zeros correspond pipeline's initial lag (the first 0 is the initial state; the second, the result of running one cycle; after that, the output is updated at every cycle):
  ..
|*)

Compute (Streams.firstn 5
           (Streams.map (fun r => r.[output_buffer])
                        system_states)). (* .unfold *)
Compute (Streams.firstn 5
           (Streams.map (fun r => @Bits.to_nat 32 r.[output_buffer])
                        system_states)). (* .unfold *)

(*|
Simulating this way is convenient for exploring small bits of code; for large designs, we have a compiler that generates optimized (but readable!) C++ that simulates Kôika designs 4 to 5 orders of magnitude faster than running directly in Coq does (a small example like this one runs hundreds of millions of simulated cycles per second in C++, and thousands in Coq):
|*)

Time Compute (@Bits.to_nat 32
             (Streams.Str_nth 1000 system_states).[output_buffer]). (* .unfold *)

(*|
Running individual rules
------------------------

We can also simulate at finer granularity: for example, here is what happens for each rule during the first cycle (each step produces a log of events that happen as part of this rule's execution):

- ``doG`` fails, because the queue is empty:
  ..
|*)

Compute (interp_rule r σ log_empty (rules doG)). (* .unfold *)

(*|
- ``doF`` succeeds and updates the queue and the input buffer:
  ..
|*)

Compute (interp_rule r σ log_empty (rules doF)). (* .unfold *)

(*|
In later cycles (here, cycle 3), ``doG`` succeeds as well and writes 1 to (port 0 of) ``queue_empty``…
|*)

Compute (let r := Streams.Str_nth 3 system_states in
         interp_rule r σ log_empty (rules doG)). (* .unfold *)

(*|
… and ``doF`` sets (port 1 of) ``queue_empty`` back to 0 as it refills the queue:
|*)

Compute (let r := Streams.Str_nth 3 system_states in
         let logG := interp_rule r σ log_empty (rules doG) in
         interp_rule r σ (must logG) (rules doF)). (* .unfold *)

(*|
Generating circuits
===================

Generating a circuit is just a matter of calling the compiler, which is a Gallina function too:
|*)

(** ``external`` is an escape hatch used to inject arbitrary Verilog
    into a design; we don't use it here **)
Definition external (r: rule_name_t) := false.

Definition circuits :=
  compile_scheduler rules external pipeline.

(*|
For printing circuits, we don't recommend using Coq's ``Compute``: our representation of circuits uses physical equality to track shared subcircuits, but Coq's printer doesn't respect sharing when printing, and hence generated circuits look giant.  Instead, we recommend looking at the generated Verilog or Dot graphs (use ``make examples/_objects/pipeline_tutorial.v/`` in the repository's root and navigate to ``examples/_objects/pipeline_tutorial.v/pipeline_tutorial.v`` to see the generated Verilog code, which uses internally instantiated modules for ``F`` and ``G`` and signature wires for ``NextInput``).

We can, however, easily compute the results produced by a circuit, either after one cycle:
|*)

Compute (interp_circuits σ circuits (lower_r r)). (* .unfold *)

(*|
… or after multiple cycles:
|*)

Definition circuit_states :=
  Streams.coiterate (interp_circuits σ circuits) (lower_r r).

Compute (Streams.firstn 5
           (Streams.map (fun r => r.[output_buffer])
                        circuit_states)). (* .unfold *)
Compute (Streams.firstn 5
           (Streams.map (fun r => @Bits.to_nat 32 r.[output_buffer])
                        circuit_states)). (* .unfold *)

(*|
Proving properties
==================

The compiler is proven correct, so we know that running a circuit will always produce the same results as running the original Kôika design.  But we haven't proved anything yet about our Kôika design, so it could be full of bugs.  Here we're interested in ruling out two types of bugs: function correctness bugs and timing bugs.

The first class of bugs would cause our design to compute something different from `g ∘ f`.  The second class of bug would cause it to stutter or lag, taking more than one cycle to produce each output.
|*)

Require Koika.CompactSemantics.
Section Correctness.

(*|
We start by quantifying over ``σ``, the model of external functions.  This matters because we want to prove our design correct regardless of the concrete functions that we plug in:
|*)

  Context (σ: forall f, Sig_denote (Sigma f)).

(*|
With this definition, ``sigma F: bits_t 32 → bits_t 32`` is the model of `f`, ``sigma G`` is the model of `g`, and ``sigma NextInput`` is the model of the `next_input` oracle.

.. coq:: none
|*)

  Arguments id _ _ / : assert.
  Arguments env_t: simpl never.
  Arguments vect: simpl never.
  Arguments may_read /.
  Arguments may_write /.
  Opaque CompactSemantics.interp_cycle.

  (* FIXME remove these notations *)
  Notation "0b0" := {| vhd := false; vtl := _vect_nil |}.
  Notation "0b1" := {| vhd := true; vtl := _vect_nil |}.

  Import StreamNotations.

(*|
Let's start by stating a specification that will rule both kinds of bugs.  In this example we completely characterize the pipeline (we have examples that use weaker characterizations such as invariants, but we haven't written a tutorial for them yet).  Note how we quantify over ``r``: as we'll see later, our design will work for any starting state, as long as the queue starts empty.
|*)

  Section Spec.
    Context (r: ContextEnv.(env_t) R).

(*|
Here is the stream of inputs consumed by the spec: we just iterate ``NextInput`` on the original value ``r.[input_buffer]``.
|*)

    Definition spec_inputs :=
      Streams.coiterate (σ NextInput) r.[input_buffer].

(*|
Here is the expected stream of outputs, which we call “observations”.  We only expect outputs to start becoming available after completing two cycles, so we simply state that the value in ``output_buffer`` should be unchanged until then:
|*)

    Definition spec_observations :=
      let composed x := σ G (σ F x) in
      r.[output_buffer] ::: (* Initial value *)
      r.[output_buffer] ::: (* Unchanged after one cycle *)
      Streams.map composed spec_inputs. (* Actual outputs *)

(*|
Here is the actual stream of states produced by the implementation, which we previously called “system_states”.  Note that we use the ``CompactSemantics`` module, which uses a more explicit representation of logs that plays more smoothly with abstract interpretation (instead of storing lists of events, it stores a record indicating whether we've read or written at port 0 and 1).

.. FIXME: use regular semantics and introduce compact ones in the proof.
|*)

    Definition impl_trace : Streams.Stream (ContextEnv.(env_t) R) :=
      Streams.coiterate
        (CompactSemantics.interp_cycle σ rules pipeline)
        r.

(*|
Finally, here is the actual stream of observations produced by the implementation:
|*)

    Definition impl_observations :=
      Streams.map (fun r => r.[output_buffer]) impl_trace.
  End Spec.

(*|
The approach we'll use in this proof is to give a complete characterization of two cycles of the pipeline, and then use k-induction for `k = 2` to generalize it into a complete characterization of the system for any number of cycles.  Here's how that looks:
|*)

  Section Proofs.

(*|
This definition captures what it means to execute one cycle:
|*)

    Definition cycle (r: ContextEnv.(env_t) R) :=
      CompactSemantics.interp_cycle σ rules pipeline r.

(*|
Here is our two-cycle characterization: if we execute our circuit twice, ``input_buffer`` takes two steps of ``NextInput``, ``queue_empty`` becomes false (regardless of where we start, the queue will be filled). ``queue_data`` contains ``f`` of the input updated by the first cycle, and ``output`` buffer contains the correct output.
|*)

    Definition phi2 (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      #{ input_buffer => σ NextInput (σ NextInput r.[input_buffer]);
         queue_empty => Ob~0;
         queue_data => σ F (σ NextInput r.[input_buffer]);
         output_buffer => σ G (σ F r.[input_buffer]) }#.

(*|
Proving this characterization is just a matter of abstract interpretation:
|*)

    Lemma phi2_correct :
      forall r, cycle (cycle r) = phi2 r.
    Proof.
      intros r; unfold cycle.

(*|
We start by unfolding the inner call to ``interp_cycle``, which yields a characterization that branches on ``r.[queue_empty]``:
|*)

      abstract_simpl r. (* .unfold *)

(*|
There are three cases: ``negb (Bits.single r.[queue_empty])``, in which both ``doG`` and ``doF`` execute; ``Bits.single r.[queue_empty]``, in which only ``doF`` executes; and an impossible third case in which neither rule would have executed.

To explore these cases we do a case split on ``r.[queue_empty]``, and simplify to show that they lead to the same result:
|*)

      destruct (Bits.single r.[queue_empty]); abstract_simpl. (* .unfold *)
      all: reflexivity.
    Qed.

(*|
With this done, we can now prove a stronger characterization that holds for any number of cycles:
|*)

    Definition phi_iterated n
               (r: ContextEnv.(env_t) R)
      : ContextEnv.(env_t) R :=
      let input := r.[input_buffer] in
      #{ input_buffer => iterate (S (S n)) (σ NextInput) input;
         queue_empty => Ob~0;
         queue_data => σ F (iterate (S n) (σ NextInput) input);
         output_buffer => σ G (σ F (iterate n (σ NextInput) input)) }#.

(*|
The proof is a two-induction (captured by the ``Div2.ind_0_1_SS`` lemma); it tells us what the registers contain after ``n + 2`` cycles of the pipeline:
|*)

    Lemma phi_iterated_correct :
      forall r n,
        iterate (S (S n)) cycle r =
        phi_iterated n r.
    Proof.
      intros r n.
      rewrite !iterate_S_acc, phi2_correct.
      revert n; apply Div2.ind_0_1_SS; simpl. (* .unfold *)
      - reflexivity.
      - unfold cycle; reflexivity.
      - intros n IH; simpl in IH; rewrite IH; reflexivity.
    Qed.

(*|
And this is enough to complete our proof!  We'll manually match up the first two states, then use our characterization.  We need to assume that the queue is empty to begin with, otherwise we'd start producing unexpected output in the first cycle;  this hypothesis comes into play when matching up the second element of the traces.
|*)

    Theorem correct_pipeline:
      forall (r: ContextEnv.(env_t) R),
        r.[queue_empty] = Ob~1 ->
        Streams.EqSt (impl_observations r) (spec_observations r).
    Proof.
      intros r Hqueue_empty.
      unfold impl_observations, spec_observations, impl_trace.

      apply Streams.ntheq_eqst; intros [ | [ | n ] ]; simpl;
        unfold spec_inputs;
        rewrite ?Streams.Str_nth_0, ?Streams.Str_nth_S,
                ?Streams.Str_nth_map, ?Streams.Str_nth_coiterate.

      - (* Initial state *) (* .unfold *)
        simpl.
        reflexivity.

      - (* After one cycle *) (* .unfold *)
        simpl.
        abstract_simpl.
        rewrite Hqueue_empty; reflexivity.

      - (* After two cycles *) (* .unfold *)
        rewrite phi_iterated_correct.
        simpl.
        reflexivity.
    Qed.
  End Proofs.
End Correctness.

(*|
Extracting to Verilog and C++
=============================

For this final piece, we need to specify which C++ and Verilog functions ``F``, ``G``, and ``NextInput`` correspond to; we do so by constructing a ``package``, which contains all relevant information:
|*)

Definition cpp_extfuns := "class extfuns {
public:
  static bits<32> next_input(bits<32> st) {
    return st + bits<32>{2};
  }

  static bits<32> f(bits<32> x) {
    return prims::slice<0, 32>(x * bits<32>{5});
  }

  static bits<32> g(bits<32> x) {
    return x + bits<32>{1};
  }
};".

Definition ext_fn_names fn :=
  match fn with
  | NextInput => "next_input"
  | F => "f"
  | G => "g"
  end.

Definition package :=
  {| ip_koika := {| koika_reg_types := R;
                   koika_reg_init reg := r.[reg];
                   koika_ext_fn_types := Sigma;
                   koika_rules := rules;
                   koika_rule_external := external;
                   koika_scheduler := pipeline;
                   koika_module_name := "pipeline_tutorial" |};

     ip_sim := {| sp_ext_fn_specs fn :=
                   {| efs_name := ext_fn_names fn;
                      efs_method := false |};
                 sp_prelude := Some cpp_extfuns |};

     ip_verilog := {| vp_ext_fn_specs fn :=
                       {| efr_name := ext_fn_names fn;
                          efr_internal :=
                            match fn with
                            | F | G => true
                            | NextInput => false
                            end |} |} |}.

(*|
This last bit registers our program, which allows the build system to locate it:
|*)

Definition prog := Interop.Backends.register package.
Extraction "pipeline_tutorial.ml" prog.

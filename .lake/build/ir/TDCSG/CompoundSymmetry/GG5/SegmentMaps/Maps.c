// Lean compiler output
// Module: TDCSG.CompoundSymmetry.GG5.SegmentMaps.Maps
// Imports: Init TDCSG.CompoundSymmetry.GG5.SegmentMaps.Generators TDCSG.CompoundSymmetry.GG5.SegmentMaps.DiskPreservation Mathlib.Analysis.Normed.Affine.Convex Mathlib.Analysis.Convex.Between Mathlib.Analysis.Convex.StrictConvexBetween Mathlib.Analysis.InnerProductSpace.Convex
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_Generators(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_DiskPreservation(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Normed_Affine_Convex(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_Between(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_Convex_StrictConvexBetween(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_InnerProductSpace_Convex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_Maps(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_Generators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_DiskPreservation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Normed_Affine_Convex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_Between(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_Convex_StrictConvexBetween(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_InnerProductSpace_Convex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

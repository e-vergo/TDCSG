// Lean compiler output
// Module: TDCSG
// Imports: Init TDCSG.Basic TDCSG.Properties TDCSG.Composition TDCSG.MeasurePreserving TDCSG.Finite TDCSG.IntervalExchange TDCSG.Examples TDCSG.Planar.Rotations TDCSG.Planar.Disks TDCSG.CompoundSymmetry.TwoDisk TDCSG.CompoundSymmetry.Finiteness TDCSG.CompoundSymmetry.GG5.Geometry TDCSG.CompoundSymmetry.GG5.SegmentMaps.Main TDCSG.CompoundSymmetry.GG5.IET TDCSG.CompoundSymmetry.GG5.CriticalRadius
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
lean_object* initialize_TDCSG_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Properties(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Composition(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_MeasurePreserving(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Finite(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_IntervalExchange(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Examples(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Planar_Rotations(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_Planar_Disks(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_TwoDisk(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_Finiteness(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_Geometry(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_Main(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_IET(uint8_t builtin, lean_object*);
lean_object* initialize_TDCSG_CompoundSymmetry_GG5_CriticalRadius(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TDCSG(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Properties(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Composition(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_MeasurePreserving(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Finite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_IntervalExchange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Examples(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Planar_Rotations(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_Planar_Disks(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_TwoDisk(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_Finiteness(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_Geometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_SegmentMaps_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_IET(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_TDCSG_CompoundSymmetry_GG5_CriticalRadius(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

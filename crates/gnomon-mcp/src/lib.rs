#![forbid(unsafe_code)]

//! Phase 2 MCP server interface exposing the 6 atomic Gnomon tools (`rmcp` + `tokio`).
//! Note: Full Phase 2 implementation begins strictly after Phase 1 Exit Gate passes.

pub const MCP_TOOL_NAMES: [&str; 6] = [
    "gnomon_lift_check",
    "gnomon_run_trace",
    "gnomon_define_op",
    "gnomon_prove_law",
    "gnomon_check_goal",
    "gnomon_consolidate",
];

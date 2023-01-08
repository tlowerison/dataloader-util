pub use dataloader_util_core::*;
pub use dataloader_util_proc_macros::*;

#[cfg(all(feature = "tracing-debug", feature = "tracing-error"))]
compile_error!(
    r#"feature "tracing-debug" and feature "tracing-error" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-debug", feature = "tracing-info"))]
compile_error!(
    r#"feature "tracing-debug" and feature "tracing-info" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-debug", feature = "tracing-trace"))]
compile_error!(
    r#"feature "tracing-debug" and feature "tracing-trace" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-debug", feature = "tracing-warn"))]
compile_error!(
    r#"feature "tracing-debug" and feature "tracing-warn" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-error", feature = "tracing-info"))]
compile_error!(
    r#"feature "tracing-error" and feature "tracing-info" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-error", feature = "tracing-trace"))]
compile_error!(
    r#"feature "tracing-error" and feature "tracing-trace" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-error", feature = "tracing-warn"))]
compile_error!(
    r#"feature "tracing-error" and feature "tracing-warn" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-info", feature = "tracing-trace"))]
compile_error!(
    r#"feature "tracing-info" and feature "tracing-trace" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-info", feature = "tracing-warn"))]
compile_error!(
    r#"feature "tracing-info" and feature "tracing-warn" cannot be enabled at the same time"#
);

#[cfg(all(feature = "tracing-trace", feature = "tracing-warn"))]
compile_error!(
    r#"feature "tracing-trace" and feature "tracing-warn" cannot be enabled at the same time"#
);

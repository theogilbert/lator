use eframe::epaint::{Color32, FontFamily, FontId, Margin};

/// The background color of the input panel.
pub const INPUT_BG_COLOR: Color32 = Color32::WHITE;
/// The background color of the results panel.
pub const RESULTS_BG_COLOR: Color32 = Color32::from_rgb(208, 208, 208);

/// The font color of the current expression.
pub const INPUT_TEXT_COLOR: Color32 = Color32::from_rgb(34, 34, 34);
/// The font color of previously submitted expressions.
pub const PREVIOUS_TEXT_COLOR: Color32 = Color32::from_rgb(68, 68, 68);
/// The font color of error messages and invalid tokens in previously submitted expressions.
pub const ERROR_TEXT_COLOR: Color32 = Color32::from_rgb(185, 48, 42);
/// The font color of the results.
pub const RESULTS_TEXT_COLOR: Color32 = Color32::from_rgb(100, 100, 100);
/// The font color of a selected expression or result.
pub const TEXT_SELECTION_COLOR: Color32 = Color32::from_rgb(34, 34, 34);

/// The ratio of the result panel's width over the whole window's.
pub const RESULTS_PANEL_RATIO: f32 = 1. / 2.3;
/// The margin around the border of each panel.
pub const PANEL_MARGIN: Margin = Margin::same(5.);
/// The font used to render text.
pub const FONT_ID: FontId = FontId::new(15.0, FontFamily::Monospace);

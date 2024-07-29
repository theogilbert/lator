use eframe::epaint::text::{TextFormat, TextWrapMode};
use eframe::epaint::{Color32, FontFamily, FontId, Margin};
use egui::text::LayoutJob;
use egui::{CentralPanel, Context, Frame, Label, SidePanel, TextBuffer, TextEdit, TextStyle};

use crate::engine::{evaluate, Error};

#[derive(Default)]
pub struct LatorApp {
    input_panel: InputPanel,
    results_panel: ResultsPanel,
}

impl LatorApp {
    const MAIN_BG_COLOR: Color32 = Color32::WHITE;
    const RESULTS_BG_COLOR: Color32 = Color32::from_rgb(250, 245, 225);

    const RESULTS_PANEL_RATIO: f32 = 1. / 2.3;
    const SEPARATOR_LINE_COLOR: Color32 = Color32::from_rgb(240, 230, 215);
    const FRAME_MARGIN: Margin = Margin::same(5.);

    const HISTORY_TEXT_COLOR: Color32 = Color32::from_rgb(100, 100, 100);
    const ERROR_TEXT_COLOR: Color32 = Color32::from_rgb(200, 30, 30);
    const TEXT_SELECTION_COLOR: Color32 = Color32::from_rgb(140, 130, 115);

    const FONT_ID: FontId = FontId::new(15.0, FontFamily::Monospace);

    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.style_mut(|style| {
            style.text_styles.insert(TextStyle::Body, Self::FONT_ID);
            style.visuals.widgets.noninteractive.bg_stroke.color = Self::SEPARATOR_LINE_COLOR;
            style.visuals.selection.bg_fill = Self::TEXT_SELECTION_COLOR;
        });

        Self::default()
    }
}

impl eframe::App for LatorApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        self.results_panel.show(ctx);

        if let Some(submitted_expression) = self.input_panel.show(ctx) {
            self.evaluate_expression(submitted_expression);
        }
    }
}

impl LatorApp {
    // Evaluate an expression submitted by the user and reflect the result in the UI.
    fn evaluate_expression(&mut self, expr: String) {
        match evaluate(&expr) {
            Ok(result) => {
                self.input_panel
                    .add_history(HistorizedExpression::Valid(expr));
                self.results_panel.add_result(result);
            }
            Err(Error::EmptyExpression()) => (), // Empty expressions are ignored.
            Err(Error::InvalidExpression(text_span)) => {
                self.input_panel
                    .add_history(HistorizedExpression::Invalid(expr, text_span));
                self.results_panel.add_result("invalid expression".into());
            }
            Err(unexpected) => {
                eprintln!("Unexpected expression evaluation error: {:?}", unexpected);
                self.input_panel
                    .add_history(HistorizedExpression::Invalid(expr, 0));
                self.results_panel.add_result("unexpected error".into());
            }
        }
    }
}

/// Displays the expression currently being typed by the user, as well as previous expressions.
#[derive(Default)]
struct InputPanel {
    /// The current expression being written by the user.
    expression: String,
    /// Previously submitted expressions
    expr_history: Vec<HistorizedExpression>,
}

enum HistorizedExpression {
    /// Denotes a valid expression.
    Valid(String),
    /// Denotes an invalid expression.
    /// The second field indicates from which position the expression is invalid.
    Invalid(String, usize),
}

impl InputPanel {
    /**
    Displays the calculator's input panel, and returns an expression if the user submitted one.
     */
    pub fn show(&mut self, ctx: &Context) -> Option<String> {
        let hist_text_format = TextFormat::simple(LatorApp::FONT_ID, LatorApp::HISTORY_TEXT_COLOR);
        let err_text_format = TextFormat::simple(LatorApp::FONT_ID, LatorApp::ERROR_TEXT_COLOR);

        let history_entries: Vec<_> = self
            .expr_history
            .iter()
            .map(|hist_expr| match hist_expr {
                HistorizedExpression::Valid(expr) => {
                    let mut layout_job = LayoutJob::default();
                    layout_job.append(expr, 0., hist_text_format.clone());
                    ctx.fonts(|fnt| fnt.layout_job(layout_job))
                }
                HistorizedExpression::Invalid(expr, invalid_start) => {
                    let mut layout_job = LayoutJob::default();
                    layout_job.append(&expr[0..*invalid_start], 0., hist_text_format.clone());
                    layout_job.append(&expr[*invalid_start..], 0., err_text_format.clone());
                    ctx.fonts(|fnt| fnt.layout_job(layout_job))
                }
            })
            .collect();

        let input_result = CentralPanel::default()
            .frame(Self::build_frame())
            .show(ctx, |ui| {
                history_entries.into_iter().for_each(|previous_expr| {
                    ui.add(Label::new(previous_expr).truncate());
                });

                let expr_edit = self.build_expr_text_edit(ctx);
                let edit_result = ui.add(expr_edit);

                let expr_submitted = edit_result.lost_focus() && !self.expression.is_empty();
                let submission = expr_submitted.then(|| self.expression.take());

                edit_result.request_focus();
                submission
            });

        input_result.inner
    }

    pub fn add_history(&mut self, expr: HistorizedExpression) {
        self.expr_history.push(expr);
    }

    fn build_frame() -> Frame {
        Frame::default()
            .fill(LatorApp::MAIN_BG_COLOR)
            .inner_margin(LatorApp::FRAME_MARGIN)
    }

    fn build_expr_text_edit(&mut self, ctx: &Context) -> TextEdit {
        TextEdit::singleline(&mut self.expression)
            .desired_width(f32::INFINITY)
            .margin(Margin::ZERO)
            .frame(false)
            .text_color(ctx.style().visuals.text_color())
            .lock_focus(true)
    }
}

/// Displays the result of submitted expressions.
///
/// Although this panel appears on the right of the InputPanel, it should be added to the UI first:
/// With egui, innermost panels should be added first ot the UI.
#[derive(Default)]
struct ResultsPanel {
    results: Vec<String>,
}

impl ResultsPanel {
    pub fn show(&mut self, ctx: &Context) {
        let ui_width = ctx.available_rect().width();
        let panel_width = (ui_width * LatorApp::RESULTS_PANEL_RATIO).floor();

        SidePanel::right("results")
            .frame(Self::build_frame())
            .exact_width(panel_width)
            .resizable(false)
            .show(ctx, |ui| {
                self.results.iter().for_each(|result| {
                    ui.add(Label::new(result).wrap_mode(TextWrapMode::Truncate));
                })
            });
    }

    pub fn add_result(&mut self, result: String) {
        self.results.push(result);
    }

    fn build_frame() -> Frame {
        Frame::default()
            .fill(LatorApp::RESULTS_BG_COLOR)
            .inner_margin(LatorApp::FRAME_MARGIN)
    }
}

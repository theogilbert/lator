use crate::engine::evaluate;
use eframe::epaint::{Color32, FontFamily, FontId, Margin};
use egui::{CentralPanel, Context, Frame, Label, SidePanel, TextBuffer, TextEdit, TextStyle};

#[derive(Default)]
pub struct LatorApp {
    input_panel: InputPanel,
    results_panel: ResultsPanel,
}

impl LatorApp {
    const FRAME_MARGIN: Margin = Margin::same(5.);
    const MAIN_BG_COLOR: Color32 = Color32::WHITE;
    const TEXT_SELECTION_COLOR: Color32 = Color32::from_rgb(140, 130, 115);
    const SEPARATOR_LINE_COLOR: Color32 = Color32::from_rgb(240, 230, 215);
    const RESULTS_BG_COLOR: Color32 = Color32::from_rgb(250, 245, 225);
    const RESULTS_PANEL_RATIO: f32 = 1. / 2.5;

    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.style_mut(|style| {
            style
                .text_styles
                .insert(TextStyle::Body, FontId::new(15.0, FontFamily::Monospace));
            style.visuals.widgets.noninteractive.bg_stroke.color = Self::SEPARATOR_LINE_COLOR;
            style.visuals.selection.bg_fill = Self::TEXT_SELECTION_COLOR;
        });

        Self::default()
    }
}

impl eframe::App for LatorApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        self.results_panel.show(ctx);
        let result = self.input_panel.show(ctx);

        if let Some(expr_result) = result {
            self.results_panel.add_result(expr_result);
        }
    }
}

/// Displays the expression currently being typed by the user, as well as previous expressions.
#[derive(Default)]
struct InputPanel {
    /// The current expression being written by the user.
    expression: String,
    /// Previously submitted expressions
    expr_history: Vec<String>,
}

impl InputPanel {
    /**
    Displays the calculator's input panel, and returns an expression if the user submitted one.
     */
    pub fn show(&mut self, ctx: &Context) -> Option<String> {
        let input_result = CentralPanel::default()
            .frame(Self::build_frame())
            .show(ctx, |ui| {
                self.expr_history.iter().for_each(|previous_expr| {
                    ui.add(Label::new(previous_expr).truncate(true));
                });

                let expr_edit = self.build_expr_text_edit(ctx);
                let edit_result = ui.add(expr_edit);

                let expr_submitted = edit_result.lost_focus() && !self.expression.is_empty();
                let submission = expr_submitted.then(|| self.expression.take());

                edit_result.request_focus();
                submission
            });

        input_result.inner.and_then(|expr| {
            let evaluation_result = evaluate(&expr);
            self.expr_history.push(expr);
            evaluation_result.ok().or(Some("".into()))
        })
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
                    ui.add(Label::new(result).wrap(false).truncate(true));
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

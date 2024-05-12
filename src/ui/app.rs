use eframe::epaint::{Color32, FontFamily, FontId, Margin};
use egui::{CentralPanel, Context, Frame, Label, SidePanel, TextBuffer, TextEdit, TextStyle};

#[derive(Default)]
pub struct LatorApp {
    input_panel: InputPanel,
    results_panel: ResultsPanel,
}

impl LatorApp {
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        const SEPARATOR_LINE_COLOR: Color32 = Color32::from_rgb(240, 230, 215);
        const TEXT_SELECTION_COLOR: Color32 = Color32::from_rgb(140, 130, 115);

        cc.egui_ctx.style_mut(|style| {
            style
                .text_styles
                .insert(TextStyle::Body, FontId::new(15.0, FontFamily::Monospace));
            style.visuals.widgets.noninteractive.bg_stroke.color = SEPARATOR_LINE_COLOR;
            style.visuals.selection.bg_fill = TEXT_SELECTION_COLOR;
        });

        Self::default()
    }
}

impl eframe::App for LatorApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        self.results_panel.show(ctx);
        let result = self.input_panel.show(ctx);

        if let Some(_submission) = result {
            self.results_panel.add_result("result".into());
        }
    }
}

/// Displays the expression currently being typed by the user, as well as previous expressions.
#[derive(Default)]
struct InputPanel {
    /// The current expression being written by the user.
    input: String,
    /// Previously submitted expressions
    history: Vec<String>,
}

impl InputPanel {
    pub fn show(&mut self, ctx: &Context) -> Option<String> {
        let result = CentralPanel::default()
            .frame(Self::build_frame())
            .show(ctx, |ui| {
                self.history.iter().for_each(|previous_expr| {
                    ui.add(Label::new(previous_expr));
                });

                let text_edit = self.build_expr_text_edit(ctx);
                let result = ui.add(text_edit);

                let expr_submitted = result.lost_focus() && !self.input.is_empty();
                let submission = expr_submitted.then(|| self.input.take());

                result.request_focus();
                submission
            });

        if let Some(submission) = &result.inner {
            self.history.push(submission.clone());
        }

        result.inner
    }

    fn build_frame() -> Frame {
        const BG_COLOR: Color32 = Color32::WHITE;
        const MARGIN: Margin = Margin::same(5.);

        Frame::default().fill(BG_COLOR).inner_margin(MARGIN)
    }

    fn build_expr_text_edit(&mut self, ctx: &Context) -> TextEdit {
        TextEdit::singleline(&mut self.input)
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
        const RESULTS_PANEL_RATIO: f32 = 1. / 2.5;
        let ui_width = ctx.available_rect().width();
        let panel_width = (ui_width * RESULTS_PANEL_RATIO).floor();

        SidePanel::right("results")
            .frame(Self::build_frame())
            .exact_width(panel_width)
            .resizable(false)
            .show(ctx, |ui| {
                self.results.iter().for_each(|result| {
                    ui.add(Label::new(result));
                })
            });
    }

    pub fn add_result(&mut self, result: String) {
        self.results.push(result);
    }

    fn build_frame() -> Frame {
        const BG_COLOR: Color32 = Color32::from_rgb(250, 245, 225);
        const MARGIN: Margin = Margin::same(5.);

        Frame::default().fill(BG_COLOR).inner_margin(MARGIN)
    }
}

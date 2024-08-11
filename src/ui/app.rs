use std::sync::Arc;

use eframe::epaint::text::{TextFormat, TextWrapMode};
use eframe::epaint::Margin;
use egui::text::LayoutJob;
use egui::{
    CentralPanel, Context, Frame, Galley, InputState, Label, SidePanel, TextBuffer, TextEdit,
    TextStyle, Ui,
};
use egui::{Event, RichText};

use crate::engine::{evaluate, Error};
use crate::ui::theme;

#[derive(Default)]
pub struct LatorApp {
    input_panel: InputPanel,
    results_panel: ResultsPanel,
}

impl LatorApp {
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.style_mut(|style| {
            style.text_styles.insert(TextStyle::Body, theme::FONT_ID);
            style.visuals.widgets.noninteractive.bg_stroke.width = 0.;
            style.visuals.selection.bg_fill = theme::TEXT_SELECTION_COLOR;
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
                self.results_panel.add_result(Result::Value(result));
            }
            Err(Error::EmptyExpression()) => (), // Empty expressions are ignored.
            Err(Error::InvalidExpression(text_span)) => {
                self.input_panel
                    .add_history(HistorizedExpression::Invalid(expr, text_span));
                self.results_panel
                    .add_result(Result::Error("invalid expression".into()));
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
    /// Displays the calculator's input panel, and returns an expression if the user submitted one.
    pub fn show(&mut self, ctx: &Context) -> Option<String> {
        ctx.input_mut(Self::replace_symbols_in_input);

        let history_entries: Vec<_> = self
            .expr_history
            .iter()
            .map(|hist_expr| Self::layout_historized_expression(hist_expr, ctx))
            .collect();

        let input_result = CentralPanel::default()
            .frame(Self::build_frame())
            .show(ctx, |ui| {
                self.show_and_ret_submitted_expr(ui, history_entries)
            });

        input_result.inner
    }

    fn replace_symbols_in_input(input: &mut InputState) {
        for event in &mut input.events {
            match event {
                Event::Text(txt) => *event = Event::Text(Self::replace_symbols_in_text(txt)),
                Event::Paste(txt) => *event = Event::Paste(Self::replace_symbols_in_text(txt)),
                _ => {}
            }
        }
    }

    fn replace_symbols_in_text(text: &str) -> String {
        text.replace("*", "×")
    }

    fn show_and_ret_submitted_expr(
        &mut self,
        ui: &mut Ui,
        history_entries: Vec<Arc<Galley>>,
    ) -> Option<String> {
        history_entries.into_iter().for_each(|previous_expr| {
            ui.add(Label::new(previous_expr).truncate());
        });

        let expr_edit = self.build_expr_text_edit();
        let edit_result = ui.add(expr_edit);

        let mut submission = None;
        if edit_result.lost_focus() && !self.expression.is_empty() {
            submission = Some(self.expression.take());
        }

        edit_result.request_focus();
        submission
    }

    /// Produce a Galley representing the rendered historized expression.
    fn layout_historized_expression(
        hist_expr: &HistorizedExpression,
        ctx: &Context,
    ) -> Arc<Galley> {
        match hist_expr {
            HistorizedExpression::Valid(expr) => {
                let mut layout_job = LayoutJob::default();
                layout_job.append(
                    expr,
                    0.,
                    TextFormat::simple(theme::FONT_ID, theme::PREVIOUS_TEXT_COLOR),
                );
                ctx.fonts(|fnt| fnt.layout_job(layout_job))
            }
            HistorizedExpression::Invalid(expr, invalid_start) => {
                let mut layout_job = LayoutJob::default();
                layout_job.append(
                    &expr[0..*invalid_start],
                    0.,
                    TextFormat::simple(theme::FONT_ID, theme::PREVIOUS_TEXT_COLOR).clone(),
                );
                layout_job.append(
                    &expr[*invalid_start..],
                    0.,
                    TextFormat::simple(theme::FONT_ID, theme::ERROR_TEXT_COLOR).clone(),
                );
                ctx.fonts(|fnt| fnt.layout_job(layout_job))
            }
        }
    }

    pub fn add_history(&mut self, expr: HistorizedExpression) {
        self.expr_history.push(expr);
    }

    fn build_frame() -> Frame {
        Frame::default()
            .fill(theme::INPUT_BG_COLOR)
            .inner_margin(theme::PANEL_MARGIN)
    }

    fn build_expr_text_edit(&mut self) -> TextEdit {
        TextEdit::singleline(&mut self.expression)
            .desired_width(f32::INFINITY)
            .margin(Margin::ZERO)
            .frame(false)
            .text_color(theme::INPUT_TEXT_COLOR)
            .lock_focus(true)
    }
}

/// Displays the result of submitted expressions.
///
/// Although this panel appears on the right of the InputPanel, it should be added to the UI first:
/// With egui, innermost panels should be added first ot the UI.
#[derive(Default)]
struct ResultsPanel {
    results: Vec<Result>,
}

impl ResultsPanel {
    pub fn show(&mut self, ctx: &Context) {
        let ui_width = ctx.available_rect().width();
        let panel_width = (ui_width * theme::RESULTS_PANEL_RATIO).floor();

        SidePanel::right("results")
            .frame(Self::build_frame())
            .exact_width(panel_width)
            .resizable(false)
            .show(ctx, |ui| {
                self.results.iter().for_each(|result| {
                    ui.add(Self::build_label_from_result(result));
                })
            });
    }

    pub fn add_result(&mut self, result: Result) {
        self.results.push(result);
    }

    fn build_label_from_result(result: &Result) -> Label {
        let rich_text = match result {
            Result::Value(content) => {
                RichText::new(content.to_string()).color(theme::RESULTS_TEXT_COLOR)
            }
            Result::Error(content) => {
                RichText::new(content.to_string()).color(theme::ERROR_TEXT_COLOR)
            }
        };

        Label::new(rich_text).wrap_mode(TextWrapMode::Truncate)
    }

    fn build_frame() -> Frame {
        Frame::default()
            .fill(theme::RESULTS_BG_COLOR)
            .inner_margin(theme::PANEL_MARGIN)
    }
}

enum Result {
    Value(String),
    Error(String),
}

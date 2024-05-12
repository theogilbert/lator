use eframe::epaint::{Color32, FontFamily, FontId, Margin};
use egui::{CentralPanel, Context, Frame, TextEdit, TextStyle};

#[derive(Default)]
pub struct LatorApp {
    input_panel: InputPanel,
}

impl LatorApp {
    pub fn new(cc: &eframe::CreationContext<'_>) -> Self {
        cc.egui_ctx.style_mut(|style| {
            style
                .text_styles
                .insert(TextStyle::Body, FontId::new(16.0, FontFamily::Monospace));
        });

        Self::default()
    }
}

impl eframe::App for LatorApp {
    fn update(&mut self, ctx: &Context, _frame: &mut eframe::Frame) {
        self.input_panel.show(ctx);
    }
}

/// This panel represents the central part of the application.
#[derive(Default)]
struct InputPanel {
    /// The current expression being written by the user.
    input: String,
}

impl InputPanel {

    pub fn show(&mut self, ctx: &Context) {
        CentralPanel::default()
            .frame(Self::build_frame())
            .show(ctx, |ui| {
                let text_edit = self.build_expr_text_edit(ctx);

                let result = ui.add(text_edit);
                result.request_focus();
            });
    }

    fn build_frame() -> Frame {
        const BG_COLOR: Color32 = Color32::WHITE;
        const MARGIN: Margin = Margin::same(5.);
        
        Frame::default()
            .fill(BG_COLOR)
            .inner_margin(MARGIN)
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

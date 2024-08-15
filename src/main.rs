#![windows_subsystem = "windows"]

use std::process::exit;

use eframe::Theme;
use egui::ViewportBuilder;

use lator::ui::app::LatorApp;

fn main() {
    let native_options = eframe::NativeOptions {
        viewport: ViewportBuilder::default()
            .with_inner_size([400., 600.])
            .with_min_inner_size([400., 50.]),
        default_theme: Theme::Light,
        ..Default::default()
    };
    let result = eframe::run_native(
        "Lator",
        native_options,
        Box::new(|cc| Ok(Box::new(LatorApp::new(cc)))),
    );

    if result.is_err() {
        exit(1);
    }
}

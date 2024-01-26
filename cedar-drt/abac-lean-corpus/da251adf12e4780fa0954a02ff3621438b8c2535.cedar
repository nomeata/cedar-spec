permit(
  principal == a::"",
  action in [Action::"%\u{2}"],
  resource
) when {
  true
};

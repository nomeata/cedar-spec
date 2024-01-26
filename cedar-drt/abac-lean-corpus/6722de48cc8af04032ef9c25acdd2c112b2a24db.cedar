permit(
  principal == a::"",
  action in [Action::""],
  resource is a in a::""
) when {
  (true && (((Action::"" in Action::"") in Action::"") in action)) && Action::""
};

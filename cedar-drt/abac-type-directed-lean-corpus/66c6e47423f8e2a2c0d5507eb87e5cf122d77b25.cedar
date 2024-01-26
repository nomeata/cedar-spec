permit(
  principal is a in a::"\u{1b}66",
  action in [Action::"action"],
  resource
) when {
  (true && (resource has "")) && ("" == "")
};

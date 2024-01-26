@yEII("6666636z6")
permit(
  principal is a,
  action in [Action::"action"],
  resource == a::"\0\0\0\0\0\0\u{1}"
) when {
  true
};

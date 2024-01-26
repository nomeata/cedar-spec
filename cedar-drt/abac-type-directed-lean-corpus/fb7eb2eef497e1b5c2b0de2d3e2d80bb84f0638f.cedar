@G("\u{1}")
@r("")
permit(
  principal == a::"",
  action in [Action::"action"],
  resource == a::""
) when {
  true && ("" == ({"": ""}[""]))
};

permit(
  principal == a::"6",
  action == Action::"action",
  resource == a::"6"
) when {
  true && ({"\u{2}\0======": false} has "6")
};

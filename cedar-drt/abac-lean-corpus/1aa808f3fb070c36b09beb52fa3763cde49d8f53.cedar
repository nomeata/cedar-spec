permit(
  principal,
  action == Action::"action",
  resource == a::"\n\0\0\0\u{7f}\n\nnon"
) when {
  true
};

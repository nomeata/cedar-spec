permit(
  principal == a::"6666",
  action in [],
  resource == a::"6666"
) when {
  ((true && ([] == [])) && true) && false
};

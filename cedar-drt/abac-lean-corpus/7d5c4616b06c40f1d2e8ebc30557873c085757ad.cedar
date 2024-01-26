@Ahhmhnh("\u{10}\0\0\0\u{8}")
permit(
  principal == A::"pij",
  action == Action::"action",
  resource in A::"pij"
) when {
  true
};

forbid(
  principal,
  action == Action::"action",
  resource == a::"6\0"
) when {
  (true && (a::"6\0" in a::"6\0")) && (a::"6\0" in principal)
};

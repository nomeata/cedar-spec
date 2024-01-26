permit(
  principal,
  action in [Action::"action"],
  resource == a::"\0\0~j"
) when {
  (true && "") && (!principal)
};

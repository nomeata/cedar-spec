permit(
  principal == a::"jjjjjjjh###\u{6}\0\0\0\0\0\0\0###",
  action in [Action::"action"],
  resource
) when {
  true && (action in principal)
};

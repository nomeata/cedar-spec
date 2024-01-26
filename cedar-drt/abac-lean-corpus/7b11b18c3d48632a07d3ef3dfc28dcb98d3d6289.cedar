permit(
  principal,
  action,
  resource in X::"pppp\0\0\n"
) when {
  true && action
};

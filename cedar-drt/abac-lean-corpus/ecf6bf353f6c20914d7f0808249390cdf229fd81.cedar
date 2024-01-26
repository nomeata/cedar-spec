permit(
  principal in a::"j",
  action,
  resource
) when {
  true && (!(!principal))
};

permit(
  principal,
  action,
  resource == a::"jj"
) when {
  (true && a::"es") && false
};

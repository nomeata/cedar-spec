permit(
  principal,
  action,
  resource == a::""
) when {
  (true && (a::"" == false)) && principal
};

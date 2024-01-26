permit(
  principal,
  action,
  resource == a::""
) when {
  (true && (principal[""])) && principal
};

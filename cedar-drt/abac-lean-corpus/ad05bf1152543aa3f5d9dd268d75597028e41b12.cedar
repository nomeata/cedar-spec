permit(
  principal,
  action,
  resource == a::";\0\0"
) when {
  (true && (!(context in a::";\0\0"))) && A::""
};

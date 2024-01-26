permit(
  principal,
  action,
  resource == a::"0\0\0"
) when {
  (true && A::"") && (!(context < a::""))
};

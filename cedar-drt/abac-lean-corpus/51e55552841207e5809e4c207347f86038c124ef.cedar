permit(
  principal is a,
  action,
  resource
) when {
  (true && (!a::"\0\0\u{4}\0\0\0\0\0")) && a::"\0\0\u{4}\0\0\0\0\0"
};

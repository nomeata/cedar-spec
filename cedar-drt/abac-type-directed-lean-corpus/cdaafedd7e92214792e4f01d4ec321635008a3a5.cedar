permit(
  principal,
  action,
  resource == a::"\0\0\0\0"
) when {
  (true && (a::"" in action)) && ([].containsAny([]))
};

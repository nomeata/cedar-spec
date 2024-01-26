permit(
  principal,
  action in [Action::""],
  resource == a::"@\u{10}\0\0jjjj,"
) when {
  (true && ((![context, context]) == a::"@\u{10}\0\0jjjj,")) && action
};

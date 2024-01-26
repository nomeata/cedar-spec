permit(
  principal == a::"\0\0\0\0y\0\0\u{13}\0~\0\0",
  action,
  resource
) when {
  true && ([].contains(action))
};

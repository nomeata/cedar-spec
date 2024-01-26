permit(
  principal is a,
  action in [Action::""],
  resource == a::"jjj&jjj&\0j"
) when {
  true && (true.isLoopback())
};

permit(
  principal is a,
  action == Action::"action",
  resource is a
) when {
  true && (!(a::"6" has "\0\0z\r\r\r\r\r\r\r\r\r\r\r\r\r\r"))
};

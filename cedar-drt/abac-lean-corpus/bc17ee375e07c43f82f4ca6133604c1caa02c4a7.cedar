permit(
  principal == a::"jjjjjjjh###\'\0\0\0\0\0\0\0jjidjjjj",
  action in [Action::"action"],
  resource
) when {
  true && (action in principal)
};
